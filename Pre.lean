import Asm

/-!
# D2: the precomputation, composed with the assembled generator (block D)

Status: lakefile root since 2026-10-04 (imports `Asm`). See NOTES.md, "D2 PRECOMPUTATION (Pre.lean)".

The reduction machine receives only the raw input `s : List (Fin r)`. Everything else is a constant
of the program: the raw-symbol map `ι` and separator `sep` (so `x = s.map ι ++ [sep]`), the
certificate exponent `k` (`m = |s| + 1 + |s|^k`), the time constants `c, e` (`T = (m + c)^e`) and
`d = depth M` (`H = capH m T d`).

* **[LIB]** counter-view additions: `decS_*`, the multi-target transfer `xferS`, the power loop
  `pow_run` (reusing D1's `mul_run` through D3OneHot's `mulS_run`).
* **[CNT]** the counter program `cprog` and its run `cprog_run` (twelve target counters loaded).
* **[FULL]** full stacks/labels, the two embeddings, the one-label read loop `rdT` / `read_run`.
* **[COMP]** the full program `fprog`; `pre_run` reaches exactly `Asm.real_run`'s preloads.
* **[REAL]** `full_run`: raw input to `encodeCNF (Phi …)`, **no hypotheses**; `fullTM : FinTM2`,
  `initList_full`.
* **[POLY]** `IsPoly` (closure under `+`, `*`, `^`), `fullB_poly`, `full_time_poly` (one `Polynomial ℕ` bounds every run).

Not here (block A): halting cleanup to `haltList`, alphabet equivalences, choosing `r, ι, sep, k,
c, e` from the verifier, `hacc`.
-/

set_option autoImplicit false

namespace PvsNP.Pre

open PvsNP.Prog PvsNP.SATDef PvsNP.Emb Turing Function
open PvsNP.D3OH (SK SΓ st st_c st_out update_st_c update_st_nil emitS incS drainS copyS mulS
  mulS_run bud_st)
open PvsNP.D3Fam (MS)

/-! ## [LIB] Counter-view additions: decrement, multi-target transfer, the power loop -/

section CLib

variable {C : Type} [DecidableEq C] {Λ : Type} {M : Λ → TM2.Stmt (SΓ C) Λ Bool}

theorem decS_pos {self ifZero ifPos : Λ} {x : C} (hp : M self = decr (.c x) ifZero ifPos)
    (F : C → ℕ) {j : ℕ} (hx : F x = j + 1) (v : Bool) (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some ifPos, true, st (update F x j) o⟩ := by
  have := decr_run_cnt hp v (S := st F o) (u := ()) (n := j) (by simp [hx])
  rw [update_st_c] at this
  exact this

theorem decS_zero {self ifZero ifPos : Λ} {x : C} (hp : M self = decr (.c x) ifZero ifPos)
    (F : C → ℕ) (hx : F x = 0) (v : Bool) (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some ifZero, false, st F o⟩ :=
  decr_run_zero hp v (by simp [hx])

/-- Unit targets of a multi-target transfer. -/
def tg (ys : List C) : List (Σ k, SΓ C k) := ys.map fun y => ⟨.c y, ()⟩

omit [DecidableEq C] in
theorem tg_keys (ys : List C) : (tg ys).keys = ys.map SK.c := by
  simp [tg, List.keys]

omit [DecidableEq C] in
theorem tg_nodupKeys {ys : List C} (h : ys.Nodup) : (tg ys).NodupKeys := by
  unfold List.NodupKeys
  rw [tg_keys]
  exact h.map (fun _ _ h => by cases h; rfl)

theorem dlookup_tg (ys : List C) (z : C) :
    List.dlookup (SK.c z) (tg ys) = if z ∈ ys then some () else none := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
      by_cases h : z = y
      · subst h; simp [tg, List.dlookup_cons_eq]
      · rw [tg, List.map_cons, List.dlookup_cons_ne _ _ (by simpa using h)]
        rw [← tg, ih]; simp [h]

theorem dlookup_tg_out (ys : List C) : List.dlookup (SK.out) (tg ys) = none := by
  rw [List.dlookup_eq_none, tg_keys]; simp

/-- Counter function after `xfer x → ys`. -/
def xf (F : C → ℕ) (x : C) (ys : List C) : C → ℕ :=
  fun z => if z = x then 0 else if z ∈ ys then F z + F x else F z

/-- **Multi-target transfer** in the counter view: drain `x`, adding its value to every `y ∈ ys`. -/
theorem xferS {self next : Λ} {x : C} {ys : List C} (hp : M self = xfer (.c x) (tg ys) self next)
    (hnd : ys.Nodup) (hx : x ∉ ys) (F : C → ℕ) (v : Bool) (o : List Bool) :
    Run M (F x + 1) ⟨some self, v, st F o⟩ ⟨some next, false, st (xf F x ys) o⟩ := by
  have := xfer_run hp (tg_nodupKeys hnd) (by rw [tg_keys]; simpa using hx) () (F x) v (st F o) rfl
  have e : addU (tg ys) (F x) (update (st F o) (SK.c x) []) = st (xf F x ys) o := by
    funext k
    rcases k with _ | z
    · simp [addU, dlookup_tg_out]
    · simp only [addU, dlookup_tg]
      by_cases hz : z = x
      · subst hz; simp [xf, hx]
      · rw [update_of_ne (by simpa using hz)]
        by_cases hy : z ∈ ys
        · simp [xf, hz, hy, add_comm]
        · simp [xf, hz, hy]
  rw [e] at this
  exact this

/-- Power-loop stages. -/
inductive PW
  | hd
  | mul (s : MS)
  | drn
  | mv
  deriving DecidableEq, Fintype

/-- `p ← p · b^kc`: decrement `kc`; `q += p·b`; drain `p`; move `q` to `p`; repeat. -/
def powS (b kc p q ad t : C) (mk : PW → Λ) (exit : Λ) : PW → TM2.Stmt (SΓ C) Λ Bool
  | .hd => decr (.c kc) exit (mk (.mul .head))
  | .mul s => mulS p ad b q t (fun s => mk (.mul s)) (mk .drn) s
  | .drn => xfer (.c p) [] (mk .drn) (mk .mv)
  | .mv => xfer (.c q) (tg [p]) (mk .mv) (mk .hd)

/-- Step budget of the power loop (`j` rounds, start value `p`, base `b`). -/
def powB (j p b : ℕ) : ℕ := j * (p * (b + 1) ^ j * (3 * b + 5) + 5) + 1

/-- **The power loop.** From `kc = j`, `q = ad = t = 0`: ends with `p ← p · b^j`, `kc = 0`. -/
theorem pow_run {b kc p q ad t : C} {mk : PW → Λ} {exit : Λ}
    (hp : ∀ s, M (mk s) = powS b kc p q ad t mk exit s)
    (hnd : [b, kc, p, q, ad, t].Nodup) :
    ∀ (j : ℕ) (F : C → ℕ), F kc = j → F q = 0 → F ad = 0 → F t = 0 → ∀ (v : Bool) (o : List Bool),
      RunLe M (powB j (F p) (F b)) ⟨some (mk .hd), v, st F o⟩
        ⟨some exit, false, st (update (update F p (F p * F b ^ j)) kc 0) o⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hbk, hbp, hbq, hbad, hbt⟩, ⟨hkp, hkq, hkad, hkt⟩, ⟨hpq, hpad, hpt⟩, ⟨hqad, hqt⟩,
    hadt, -⟩ := hnd
  intro j
  induction j with
  | zero =>
      intro F hk hq had ht v o
      have r := decS_zero (hp .hd) F hk v o
      have hF : update (update F p (F p * F b ^ 0)) kc 0 = F := by
        funext z; by_cases h1 : z = kc
        · subst h1; simp [hk]
        · by_cases h2 : z = p
          · subst h2; simp [h1]
          · simp [h1]
      rw [hF]; exact r.le (by simp [powB])
  | succ j ih =>
      intro F hk hq had ht v o
      -- decrement
      have r1 := decS_pos (hp .hd) F hk v o
      set F1 := update F kc j with hF1
      -- q += p * b
      have r2 := mulS_run (a := p) (ad := ad) (b := b) (c := q) (t := t)
        (mk := fun s => mk (.mul s)) (next := mk .drn) (M := M) (fun s => hp (.mul s))
        (by simp [hpad, (Ne.symm hbp), hpq, hpt, (Ne.symm hbad), (Ne.symm hqad), hadt, hbq, hbt, hqt])
        F1 (by simp [hF1, (Ne.symm hkad), had]) (by simp [hF1, (Ne.symm hkt), ht]) true o
      set F2 := update F1 q (F1 p * F1 b + F1 q) with hF2
      -- drain p
      have r3 := drainS (hp .drn) F2 false o
      set F3 := update F2 p 0 with hF3
      -- move q to p
      have r4 := xferS (hp .mv) (by simp) (by simpa using (Ne.symm hpq)) F3 false o
      set F4 := xf F3 q [p] with hF4
      have hF1p : F1 p = F p := by rw [hF1, update_of_ne (Ne.symm hkp)]
      have hF1b : F1 b = F b := by rw [hF1, update_of_ne hbk]
      have hF1q : F1 q = 0 := by rw [hF1, update_of_ne (Ne.symm hkq), hq]
      have hF2p : F2 p = F p := by rw [hF2, update_of_ne hpq, hF1p]
      have hF3q : F3 q = F p * F b := by
        rw [hF3, update_of_ne (Ne.symm hpq), hF2, update_self, hF1p, hF1b, hF1q, add_zero]
      have hrest : ∀ z, z ≠ q → z ≠ p → z ≠ kc → F4 z = F z := by
        intro z h1 h2 h3
        simp only [hF4, xf, if_neg h1, List.mem_singleton, if_neg h2, hF3, hF2, hF1,
          update_of_ne h1, update_of_ne h2, update_of_ne h3]
      have h4p : F4 p = F p * F b := by
        simp only [hF4, xf, if_neg hpq, List.mem_singleton, if_true, hF3, update_self, zero_add]
        exact hF3q
      have h4k : F4 kc = j := by
        simp only [hF4, xf, if_neg hkq, List.mem_singleton, if_neg hkp, hF3, hF2, hF1,
          update_of_ne hkp, update_of_ne hkq, update_self]
      have h4b : F4 b = F b := hrest b hbq hbp hbk
      have r5 := ih F4 h4k (by simp [hF4, xf])
        (by rw [hrest ad (Ne.symm hqad) (Ne.symm hpad) (Ne.symm hkad), had])
        (by rw [hrest t (Ne.symm hqt) (Ne.symm hpt) (Ne.symm hkt), ht]) false o
      have hend : update (update F4 p (F4 p * F4 b ^ j)) kc 0 =
          update (update F p (F p * F b ^ (j + 1))) kc 0 := by
        funext z
        by_cases h1 : z = kc
        · subst h1; simp
        rw [update_of_ne h1, update_of_ne h1]
        by_cases h2 : z = p
        · subst h2; rw [update_self, update_self, h4p, h4b, pow_succ]; ring
        rw [update_of_ne h2, update_of_ne h2]
        by_cases h3 : z = q
        · subst h3; simp [hF4, xf, hq]
        exact hrest z h3 h2 h1
      rw [hend, h4p, h4b] at r5
      rw [hF2p] at r3
      rw [hF3q] at r4
      rw [hF1p, hF1b] at r2
      have := ((((r1.le le_rfl).trans (r2.le le_rfl)).trans (r3.le le_rfl)).trans
        (r4.le le_rfl)).trans r5
      refine this.mono ?_
      unfold powB
      have hpw : F p * F b * (F b + 1) ^ j ≤ F p * (F b + 1) ^ (j + 1) := by
        rw [pow_succ, mul_assoc, mul_comm (F b)]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_succ _))
      have hp1 : F p ≤ F p * (F b + 1) ^ (j + 1) :=
        Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.succ_pos _))
      have h1 := Nat.mul_le_mul_right (3 * F b + 5) hp1
      have h2 := Nat.mul_le_mul_left j (Nat.add_le_add_right
        (Nat.mul_le_mul_right (3 * F b + 5) hpw) 5)
      nlinarith [h1, h2]

end CLib

/-! ## [CNT] The precomputation's counter program -/

/-- Scratch counters. -/
inductive PS
  | N | P | Q | AD | TMP | KC | Mc | B | Tc | Fx | Dd | Hc
  deriving DecidableEq, Fintype

/-- Target counters (the twelve preloads of `Asm.real_run`). -/
inductive PT
  | uT | uH | sT | sH | hT | hH | aT | aH | iT | iX | iE | iF
  deriving DecidableEq, Fintype

/-- All counters of the counter program. -/
inductive CC
  | s (x : PS)
  | t (y : PT)
  deriving DecidableEq, Fintype

/-- Labels of the counter program. -/
inductive PL
  | p1 | k1 | w1 (s : PW) | x1 | x2 | x3 | x4 | c1 | c2 | x6 | x7 | x8 | w2 (s : PW) | x9
  | ml (s : MS) | x10 | x11 | x12 | x13 | x14 | done
  deriving DecidableEq, Fintype

open CC PS PT in
/-- **The counter program**: `P = n^k`, `m = n + 1 + P`, `T = (m + c)^e`, `F = d·T + d + 1`,
`H = m + F`, then the twelve loads. -/
def cprog (k c e d : ℕ) : PL → TM2.Stmt (SΓ CC) PL Bool
  | .p1 => emitR (.c (s P)) (List.replicate 1 ()) .k1
  | .k1 => emitR (.c (s KC)) (List.replicate k ()) (.w1 .hd)
  | .w1 q => powS (s N) (s KC) (s P) (s Q) (s AD) (s TMP) PL.w1 .x1 q
  | .x1 => xfer (.c (s P)) (tg [s Mc, t iE]) .x1 .x2
  | .x2 => xfer (.c (s N)) (tg [s Mc, t iX]) .x2 .x3
  | .x3 => emitR (.c (s Mc)) (List.replicate 1 ()) .x4
  | .x4 => emitR (.c (t iX)) (List.replicate 1 ()) .c1
  | .c1 => xfer (.c (s Mc)) [⟨.c (s B), ()⟩, ⟨.c (s TMP), ()⟩] .c1 .c2
  | .c2 => xfer (.c (s TMP)) [⟨.c (s Mc), ()⟩] .c2 .x6
  | .x6 => emitR (.c (s B)) (List.replicate c ()) .x7
  | .x7 => emitR (.c (s KC)) (List.replicate e ()) .x8
  | .x8 => emitR (.c (s Tc)) (List.replicate 1 ()) (.w2 .hd)
  | .w2 q => powS (s B) (s KC) (s Tc) (s Q) (s AD) (s TMP) PL.w2 .x9 q
  | .x9 => emitR (.c (s Dd)) (List.replicate d ()) (.ml .head)
  | .ml q => mulS (s Dd) (s AD) (s Tc) (s Fx) (s TMP) PL.ml .x10 q
  | .x10 => emitR (.c (s Fx)) (List.replicate (d + 1) ()) .x11
  | .x11 => xfer (.c (s Fx)) (tg [s Hc, t iF]) .x11 .x12
  | .x12 => xfer (.c (s Mc)) (tg [s Hc]) .x12 .x13
  | .x13 => xfer (.c (s Tc)) (tg [t uT, t sT, t hT, t aT, t iT]) .x13 .x14
  | .x14 => xfer (.c (s Hc)) (tg [t uH, t sH, t hH, t aH]) .x14 .done
  | .done => .halt

/-- `m = n + 1 + n^k` (so `|x ++ y| ≤ m ↔ |y| ≤ n^k` for `|x| = n + 1`). -/
def mOf (k n : ℕ) : ℕ := n + 1 + n ^ k

/-- `T = (m + c)^e`. -/
def TOf (k c e n : ℕ) : ℕ := (mOf k n + c) ^ e

/-- Start: `N = n`. -/
def F0 (n : ℕ) : CC → ℕ
  | .s .N => n
  | _ => 0

/-- After the first power loop. -/
def F1 (k n : ℕ) : CC → ℕ
  | .s .N => n
  | .s .P => n ^ k
  | _ => 0

/-- Before the second power loop. -/
def F2 (k c e n : ℕ) : CC → ℕ
  | .s .Mc => mOf k n
  | .s .B => mOf k n + c
  | .s .KC => e
  | .s .Tc => 1
  | .t .iX => n + 1
  | .t .iE => n ^ k
  | _ => 0

/-- After the second power loop. -/
def F3 (k c e n : ℕ) : CC → ℕ
  | .s .Mc => mOf k n
  | .s .B => mOf k n + c
  | .s .Tc => TOf k c e n
  | .t .iX => n + 1
  | .t .iE => n ^ k
  | _ => 0

/-- Target values (`Fx = d·T + d + 1 = H - m`, `H = capH m T d`). -/
def tv (k c e d n : ℕ) : PT → ℕ
  | .uT | .sT | .hT | .aT | .iT => TOf k c e n
  | .uH | .sH | .hH | .aH => Sit.capH (mOf k n) (TOf k c e n) d
  | .iX => n + 1
  | .iE => n ^ k
  | .iF => (TOf k c e n + 1) * d + 1

/-- End: targets loaded; leftovers `B = m + c`, `Dd = d`. -/
def F4 (k c e d n : ℕ) : CC → ℕ
  | .s .B => mOf k n + c
  | .s .Dd => d
  | .t y => tv k c e d n y
  | _ => 0

/-- Step budget of the counter program. -/
def cB (k c e d n : ℕ) : ℕ :=
  2 + powB k 1 n + (n ^ k + 1) + (n + 1) + 2 + (2 * mOf k n + 2) + 3 + powB e 1 (mOf k n + c) +
    1 + (d * (2 * TOf k c e n + 3) + d + 2) + 1 + (d * TOf k c e n + d + 2) + (mOf k n + 1) +
    (TOf k c e n + 1) + (Sit.capH (mOf k n) (TOf k c e n) d + 1)

open CC PS PT in
/-- **The counter program's run**: from `N = n` to the twelve loaded targets. -/
theorem cprog_run (k c e d n : ℕ) (v : Bool) (o : List Bool) :
    RunLe (cprog k c e d) (cB k c e d n) ⟨some .p1, v, st (F0 n) o⟩
      ⟨some .done, false, st (F4 k c e d n) o⟩ := by
  refine Bud.start ?_
  refine (emitS (M := cprog k c e d) (self := .p1) (next := .k1) rfl _ _ _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .k1) (next := .w1 .hd) rfl _ _ _).bud ?_
  refine (pow_run (M := cprog k c e d) (mk := PL.w1) (exit := .x1) (fun _ => rfl) (by decide) k _
    (by simp [F0]) (by simp [F0]) (by simp [F0]) (by simp [F0]) _ _).bud ?_
  refine bud_st (F' := F1 k n) (by funext z; rcases z with z | z <;> cases z <;> simp [F0, F1]) ?_
  refine (xferS (M := cprog k c e d) (self := .x1) (next := .x2) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine (xferS (M := cprog k c e d) (self := .x2) (next := .x3) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x3) (next := .x4) rfl _ _ _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x4) (next := .c1) rfl _ _ _).bud ?_
  refine (copyS (M := cprog k c e d) (l₁ := .c1) (l₂ := .c2) (next := .x6) rfl rfl (by decide)
    (by decide) (by decide) _ (by simp [xf, F1]) _ _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x6) (next := .x7) rfl _ _ _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x7) (next := .x8) rfl _ _ _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x8) (next := .w2 .hd) rfl _ _ _).bud ?_
  refine bud_st (F' := F2 k c e n) (by
    funext z; rcases z with z | z <;> cases z <;> simp [xf, F1, F2, mOf] <;> omega) ?_
  refine (pow_run (M := cprog k c e d) (mk := PL.w2) (exit := .x9) (fun _ => rfl) (by decide) e _
    (by simp [F2]) (by simp [F2]) (by simp [F2]) (by simp [F2]) _ _).bud ?_
  refine bud_st (F' := F3 k c e n) (by
    funext z; rcases z with z | z <;> cases z <;> simp [F2, F3, TOf]) ?_
  refine (emitS (M := cprog k c e d) (self := .x9) (next := .ml .head) rfl _ _ _).bud ?_
  refine (mulS_run (M := cprog k c e d) (mk := PL.ml) (next := .x10) (fun _ => rfl) (by decide) _
    (by simp [F3]) (by simp [F3]) _ _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x10) (next := .x11) rfl _ _ _).bud ?_
  refine (xferS (M := cprog k c e d) (self := .x11) (next := .x12) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine (xferS (M := cprog k c e d) (self := .x12) (next := .x13) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine (xferS (M := cprog k c e d) (self := .x13) (next := .x14) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine (xferS (M := cprog k c e d) (self := .x14) (next := .done) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine Bud.fin ?_ ?_
  · simp [xf, F0, F1, F2, F3, cB, Sit.capH, mOf]
    generalize TOf k c e n = T
    linarith
  · congr 2
    funext z; rcases z with z | z <;> cases z <;> simp [xf, F3, F4, tv, Sit.capH] <;> ring


/-! ## [FULL] The full machine: read loop, counter program, host -/

open PvsNP.Asm

/-- Full stacks: the host's, the raw input, the private scratch counters. -/
inductive FK
  | h (k : HK)
  | raw
  | pc (x : PS)
  deriving DecidableEq, Fintype

abbrev FΓ (g r : ℕ) : FK → Type
  | .h k => HΓ g k
  | .raw => Fin r
  | .pc _ => Unit

/-- Full labels: the read loop, the counter program, the host. -/
inductive FL (Λ : Type)
  | rd
  | pre (l : PL)
  | h (l : Λ)
  deriving DecidableEq, Fintype

/-- Host counter receiving each target. -/
def tgt : PT → HK
  | .uT => .up .Tn
  | .uH => .up .Hs
  | .sT => .sd .Tn
  | .sH => .sd .Hs
  | .hT => .sh .Tn
  | .hH => .sh .Hs
  | .aT => .ac .Tn
  | .aH => .ac .Hs
  | .iT => .ini .Tn
  | .iX => .ini .Xn
  | .iE => .ini .En
  | .iF => .ini .Fn

def eC : SK CC → FK
  | .out => .h .out
  | .c (.s x) => .pc x
  | .c (.t y) => .h (tgt y)

section Embs

variable (g r : ℕ)

/-- The counter program's stacks inside the full machine. -/
def embC : SEmb (SΓ CC) (FΓ g r) where
  e := eC
  inj := by
    intro a b h
    rcases a with _ | (x | y) <;> rcases b with _ | (x' | y') <;>
      simp only [eC, FK.h.injEq, FK.pc.injEq, reduceCtorEq] at h ⊢
    all_goals first
      | exact h
      | (subst h; rfl)
      | (cases y <;> cases h)
      | (cases y' <;> cases h)
      | (cases y <;> cases y' <;> first | rfl | cases h)
  ι := fun k => match k with
    | .out => Equiv.refl _
    | .c (.s _) => Equiv.refl _
    | .c (.t y) => match y with
      | .uT | .uH | .sT | .sH | .hT | .hH | .aT | .aH | .iT | .iX | .iE | .iF => Equiv.refl _

/-- The host's stacks inside the full machine. -/
def embH : SEmb (HΓ g) (FΓ g r) where
  e := FK.h
  inj := fun _ _ h => by cases h; rfl
  ι := fun _ => Equiv.refl _

end Embs

section Read

variable {g r : ℕ} {Λ : Type}

/-- **The read loop** (one label, one step per symbol). A peek-chain over the raw alphabet finds
the top symbol `i`, pops it, pushes its code `cf i` on `inp` and one unit on `N`. On empty input
it pushes the separator code `cs` and starts the counter program. -/
def rdT (cf : Fin r → Fin g) (cs : Fin g) : List (Fin r) → TM2.Stmt (FΓ g r) (FL Λ) Bool
  | [] => .push (.h .inp) (fun _ => cs) (.load (fun _ => false) (.goto fun _ => .pre .p1))
  | i :: L => .peek .raw (fun _ o => decide (o = some i))
      (.branch id (.pop .raw (fun v _ => v) (.push (.h .inp) (fun _ => cf i)
        (.push (.pc .N) (fun _ => ()) (.goto fun _ => .rd)))) (rdT cf cs L))

/-- Stacks during the read loop: rest of the input, codes so far, `N = n`, output `o`. -/
def fst (s : List (Fin r)) (ins : List (Fin g)) (n : ℕ) (o : List Bool) : ∀ k, List (FΓ g r k)
  | .raw => s
  | .h .inp => ins
  | .h .out => o
  | .pc .N => cnt () n
  | _ => []

theorem rdT_hit (cf : Fin r → Fin g) (cs : Fin g) (a : Fin r) (s : List (Fin r))
    (ins : List (Fin g)) (n : ℕ) (o : List Bool) :
    ∀ (L : List (Fin r)), a ∈ L → ∀ v : Bool,
      TM2.stepAux (rdT (Λ := Λ) cf cs L) v (fst (a :: s) ins n o) =
        ⟨some .rd, true, fst s (cf a :: ins) (n + 1) o⟩ := by
  intro L
  induction L with
  | nil => intro h; cases h
  | cons i L ih =>
      intro h v
      by_cases hi : a = i
      · subst hi
        simp only [rdT, TM2.stepAux]
        simp only [fst, List.head?_cons, decide_true, id, cond_true, List.tail_cons]
        congr 1
        funext k
        rcases k with k | _ | x
        · cases k <;> simp [fst]
        · simp [fst]
        · cases x <;> simp [fst, cnt_succ]
      · have hL : a ∈ L := by
          rcases List.mem_cons.1 h with h | h
          · exact absurd h hi
          · exact h
        simp only [rdT, TM2.stepAux]
        simp only [fst, List.head?_cons, Option.some.injEq, hi, decide_false, id, cond_false]
        exact ih hL false

theorem rdT_nil (cf : Fin r → Fin g) (cs : Fin g) (ins : List (Fin g)) (n : ℕ) (o : List Bool) :
    ∀ (L : List (Fin r)) (v : Bool),
      TM2.stepAux (rdT (Λ := Λ) cf cs L) v (fst [] ins n o) =
        ⟨some (.pre .p1), false, fst [] (cs :: ins) n o⟩ := by
  intro L
  induction L with
  | nil =>
      intro v
      simp only [rdT, TM2.stepAux]
      congr 1
      funext k
      rcases k with k | _ | x
      · cases k <;> simp [fst]
      · simp [fst]
      · cases x <;> simp [fst]
  | cons i L ih =>
      intro v
      simp only [rdT, TM2.stepAux]
      simp only [fst, List.head?_nil, reduceCtorEq, decide_false, id, cond_false]
      exact ih false

/-- **The read loop's run**: `|s| + 1` steps; afterwards `inp = cs :: rev (cf s) ++ ins`. -/
theorem read_run {M : FL Λ → TM2.Stmt (FΓ g r) (FL Λ) Bool} {cf : Fin r → Fin g} {cs : Fin g}
    (hM : M .rd = rdT cf cs (List.finRange r)) (o : List Bool) :
    ∀ (s : List (Fin r)) (ins : List (Fin g)) (n : ℕ) (v : Bool),
      Run M (s.length + 1) ⟨some .rd, v, fst s ins n o⟩
        ⟨some (.pre .p1), false, fst [] (cs :: ((s.map cf).reverse ++ ins)) (n + s.length) o⟩ := by
  intro s
  induction s with
  | nil =>
      intro ins n v
      refine Run.single ?_
      simp [hM, rdT_nil]
  | cons a s ih =>
      intro ins n v
      have := ih (cf a :: ins) (n + 1) true
      rw [show (s.map cf).reverse ++ cf a :: ins = ((a :: s).map cf).reverse ++ ins by simp,
        show n + 1 + s.length = n + (a :: s).length by simp; omega] at this
      refine Run.head ?_ this
      simp only [TM2.step, hM, rdT_hit cf cs a s ins n o _ (List.mem_finRange a)]

end Read


/-! ## [COMP] The full program and its run -/

section Comp

variable {g r : ℕ} {Λ : Type}

/-- **The full program**: read loop, then the counter program (embedded on its own counters and
the twelve host targets), then the host program `hp` from `start`. -/
def fprog (cf : Fin r → Fin g) (cs : Fin g) (k c e d : ℕ) (hp : Λ → TM2.Stmt (HΓ g) Λ Bool)
    (start : Λ) : FL Λ → TM2.Stmt (FΓ g r) (FL Λ) Bool
  | .rd => rdT cf cs (List.finRange r)
  | .pre l => if l = .done then .load (fun _ => false) (.goto fun _ => .h start)
      else mapS (embC g r) FL.pre (cprog k c e d l)
  | .h l => mapS (embH g r) FL.h (hp l)

variable {cf : Fin r → Fin g} {cs : Fin g} {k c e d : ℕ} {hp : Λ → TM2.Stmt (HΓ g) Λ Bool}
  {start : Λ}

theorem embeds_C : Embeds (embC g r) FL.pre (cprog k c e d) (fprog cf cs k c e d hp start) := by
  intro l
  by_cases hl : l = .done
  · exact Or.inr (by subst hl; rfl)
  · exact Or.inl (by simp only [fprog, if_neg hl])

theorem embeds_H : Embeds (embH g r) FL.h hp (fprog cf cs k c e d hp start) :=
  fun _ => Or.inl rfl

theorem agree_C (ins : List (Fin g)) (n : ℕ) (o : List Bool) :
    Agree (embC g r) (st (F0 n) o) (fst [] ins n o) := by
  intro k
  rcases k with _ | (x | y)
  · exact (List.map_id _).symm
  · cases x <;> exact (List.map_id _).symm
  · cases y <;> exact (List.map_id _).symm

theorem eC_ne_inp (k : SK CC) : eC k ≠ .h .inp := by
  rcases k with _ | (x | y) <;> simp [eC]
  cases y <;> simp [tgt]

/-- **The precomputation** (read loop + counter program + one chaining step): from the raw input
`s`, the full machine reaches the host's start label with exactly `real_run`'s preloads: `out`
unchanged, `inp = cs :: rev (cf s)`, every target `tgt y` holding `tv … y`, every other host
stack empty. -/
theorem pre_run (s : List (Fin r)) (o : List Bool) :
    ∃ S : ∀ k, List (FΓ g r k),
      RunLe (fprog cf cs k c e d hp start) (s.length + 1 + cB k c e d s.length + 1)
        ⟨some .rd, false, fst s [] 0 o⟩ ⟨some (.h start), false, S⟩ ∧
      S (.h .out) = o ∧ S (.h .inp) = cs :: (s.map cf).reverse ∧
      (∀ y, (S (.h (tgt y))).length = tv k c e d s.length y) ∧
      (∀ hk, (∀ y, tgt y ≠ hk) → hk ≠ .out → hk ≠ .inp → S (.h hk) = []) := by
  have r1 := read_run (M := fprog cf cs k c e d hp start) rfl o s [] 0 false
  rw [List.append_nil, Nat.zero_add] at r1
  obtain ⟨T1, r2, a2, f2⟩ := runLe_embed (E := embC g r) FL.pre embeds_C
    (cprog_run k c e d s.length false o) (agree_C _ _ o)
  have r3 : Run (fprog cf cs k c e d hp start) 1 ⟨some (.pre .done), false, T1⟩
      ⟨some (.h start), false, T1⟩ :=
    Run.single (by simp [fprog, TM2.stepAux])
  refine ⟨T1, ((r1.le le_rfl).trans r2).trans (r3.le le_rfl), (a2 .out).trans (List.map_id _),
    ?_, fun y => by
      have := congrArg List.length (a2 (.c (.t y)))
      rw [List.length_map] at this
      exact this.trans (by simp [F4]), fun hk h1 h2 h3 => ?_⟩
  · exact (f2 _ eC_ne_inp).trans rfl
  · rw [f2 _ (fun k => by
      rcases k with _ | (x | y)
      · exact fun h => h2 (FK.h.inj h).symm
      · simp [embC, eC]
      · exact fun h => h1 y (FK.h.inj h))]
    cases hk with
    | out => exact absurd rfl h2
    | inp => exact absurd rfl h3
    | _ => rfl

end Comp


/-! ## [REAL] The full machine on the real generators: raw input to emitted formula -/

section Real

open PvsNP.Sit

variable {r : ℕ} {M : FinTM2} (E : Enc M)

/-- The full program on the real generators of `M`: raw symbols are coded by `encF E ∘ ι`, the
separator by `encF E sep`; `d = depth M`. -/
noncomputable abbrev fullProg (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k c e : ℕ) :=
  fprog (fun i => D3Init.encF E (ι i)) (D3Init.encF E sep) k c e (depth M) (realProg E Ys acc)
    (.ini (.pre1 .eg))

/-- Step bound of the full machine on an input of length `n`. -/
noncomputable def fullB (Ys : List (M.Γ M.k₀)) (k c e n : ℕ) : ℕ :=
  n + 1 + cB k c e (depth M) n + 1 + realB E Ys (mOf k n) (TOf k c e n)

theorem cnt_of_len {l : List Unit} {n : ℕ} (h : l.length = n) : l = cnt () n :=
  List.eq_replicate_iff.2 ⟨h, fun _ _ => rfl⟩

/-- **The composed machine, raw input to formula.** From the raw input `s` (all other stacks
empty, output `o`), the full machine halts its host part at `fin` within `fullB` steps, having
prepended exactly `encodeCNF (Phi …)` for `x = s.map ι ++ [sep]`, `m = |s| + 1 + |s|^k`,
`T = (m + c)^e`. **No hypotheses** (`|x| ≤ m` is discharged here). -/
theorem full_run (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀) (sep : M.Γ M.k₀)
    (k c e : ℕ) (s : List (Fin r)) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (FΓ E.layout.g r k)),
      RunLe (fullProg E Ys acc ι sep k c e) (fullB E Ys k c e s.length)
        ⟨some .rd, false, fst s [] 0 o⟩ ⟨some (.h .fin), v, S⟩ ∧
      S (.h .out) = encodeCNF (Phi E (s.map ι ++ [sep]) Ys acc (mOf k s.length)
        (TOf k c e s.length)) ++ o := by
  obtain ⟨T1, r1, ho, hin, ht, hz⟩ := pre_run (cf := fun i => D3Init.encF E (ι i))
    (cs := D3Init.encF E sep) (k := k) (c := c) (e := e) (d := depth M) (hp := realProg E Ys acc)
    (start := .ini (.pre1 .eg)) s o
  have e1 : (s.map ι ++ [sep]).length = s.length + 1 := by simp
  have hx : (s.map ι ++ [sep]).length ≤ mOf k s.length := by rw [e1, mOf]; omega
  have e2 : mOf k s.length - (s.length + 1) = s.length ^ k := by rw [mOf]; omega
  have e3 : capH (mOf k s.length) (TOf k c e s.length) (depth M) - mOf k s.length =
      (TOf k c e s.length + 1) * depth M + 1 := by unfold capH; omega
  have nt : ∀ hk : HK, (∀ y, tgt y ≠ hk) → hk ≠ .out → hk ≠ .inp →
      T1 (.h hk) = [] := hz
  obtain ⟨v, S, hr, hout⟩ := real_run E (s.map ι ++ [sep]) Ys acc (mOf k s.length)
    (TOf k c e s.length) hx (fun hk => T1 (.h hk)) o ho
    (hin.trans (by simp [List.map_append, List.reverse_append]))
    (fun z => by
      cases z
      case Tn => exact cnt_of_len (ht .uT)
      case Hs => exact cnt_of_len (ht .uH)
      all_goals exact nt _ (by intro y; cases y <;> simp [tgt]) (by simp) (by simp))
    (fun z => by
      cases z
      case Tn => exact cnt_of_len (ht .sT)
      case Hs => exact cnt_of_len (ht .sH)
      all_goals exact nt _ (by intro y; cases y <;> simp [tgt]) (by simp) (by simp))
    (fun z => by
      cases z
      case Tn => exact cnt_of_len (ht .hT)
      case Hs => exact cnt_of_len (ht .hH)
      all_goals exact nt _ (by intro y; cases y <;> simp [tgt]) (by simp) (by simp))
    (fun z => by
      cases z
      case Tn => exact cnt_of_len (ht .aT)
      case Hs => exact cnt_of_len (ht .aH)
      all_goals exact nt _ (by intro y; cases y <;> simp [tgt]) (by simp) (by simp))
    (fun z => by
      rw [e1, e2, e3]
      cases z
      case Tn => exact cnt_of_len (ht .iT)
      case Xn => exact cnt_of_len (ht .iX)
      case En => exact cnt_of_len (ht .iE)
      case Fn => exact cnt_of_len (ht .iF)
      all_goals exact nt _ (by intro y; cases y <;> simp [tgt]) (by simp) (by simp))
  obtain ⟨T2, r2, a2, -⟩ := runLe_embed (E := embH E.layout.g r) FL.h embeds_H hr
    (S' := T1) (fun _ => (List.map_id _).symm)
  exact ⟨v, T2, r1.trans r2, ((a2 .out).trans (List.map_id _)).trans hout⟩

/-- **The full machine as a genuine `FinTM2`**: input stack `raw`, output stack `h out`. -/
noncomputable def fullTM (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k c e : ℕ) : FinTM2 where
  K := FK
  k₀ := .raw
  k₁ := .h .out
  Γ := FΓ E.layout.g r
  Λ := FL _
  main := .rd
  σ := Bool
  initialState := false
  m := fullProg E Ys acc ι sep k c e

/-- `initList` of the full machine is the read loop's start configuration. -/
theorem initList_full (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k c e : ℕ) (s : List (Fin r)) :
    initList (fullTM E Ys acc ι sep k c e) s = ⟨some .rd, false, fst s [] 0 []⟩ := by
  simp only [initList]
  congr 1
  funext q
  rcases q with q | _ | x
  · cases q <;> rfl
  · rfl
  · cases x <;> rfl

end Real

/-! ## [POLY] The step bound is a polynomial in `|s|` -/

/-- `f` is (pointwise) the evaluation of a polynomial with natural coefficients. -/
def IsPoly (f : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ n, f n = p.eval n

namespace IsPoly

theorem const (a : ℕ) : IsPoly fun _ => a := ⟨Polynomial.C a, fun _ => by simp⟩

theorem id : IsPoly fun n => n := ⟨Polynomial.X, fun _ => by simp⟩

theorem add {f g : ℕ → ℕ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly fun n => f n + g n := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg; exact ⟨p + q, fun n => by simp [hp, hq]⟩

theorem mul {f g : ℕ → ℕ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly fun n => f n * g n := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg; exact ⟨p * q, fun n => by simp [hp, hq]⟩

theorem pow {f : ℕ → ℕ} (hf : IsPoly f) (j : ℕ) : IsPoly fun n => f n ^ j := by
  obtain ⟨p, hp⟩ := hf; exact ⟨p ^ j, fun n => by simp [hp]⟩

end IsPoly

theorem fullB_poly {M : FinTM2} (E : Sit.Enc M) (Ys : List (M.Γ M.k₀)) (k c e : ℕ) :
    IsPoly (fullB E Ys k c e) := by
  unfold fullB
  simp only [cB, powB, realB, TOf, mOf, Sit.capH]
  generalize D3Init.initC _ _ _ = A1
  generalize D3Fam.genC _ _ = A2
  generalize D3SH.shC _ _ = A3
  generalize D3Acc.accC _ _ _ = A4
  generalize Sit.depth M = d
  -- leaves are `n`, constants (generalized above, so no unfolding), `+`, `*`, `^ const`
  repeat' first
    | with_reducible exact IsPoly.const _
    | with_reducible exact IsPoly.id
    | with_reducible apply IsPoly.add
    | with_reducible apply IsPoly.mul
    | with_reducible apply IsPoly.pow

/-- **Polynomial time bound of the composed machine**: one polynomial `p` (depending only on the
machine's constants) bounds the step count on every raw input. -/
theorem full_time_poly {r : ℕ} {M : FinTM2} (E : Sit.Enc M) (Ys : List (M.Γ M.k₀))
    (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀) (sep : M.Γ M.k₀) (k c e : ℕ) :
    ∃ p : Polynomial ℕ, ∀ (s : List (Fin r)) (o : List Bool), ∃ (v : Bool) (S : ∀ k, List (FΓ E.layout.g r k)),
      RunLe (fullProg E Ys acc ι sep k c e) (p.eval s.length)
        ⟨some .rd, false, fst s [] 0 o⟩ ⟨some (.h .fin), v, S⟩ ∧
      S (.h .out) = encodeCNF (Phi E (s.map ι ++ [sep]) Ys acc (mOf k s.length)
        (TOf k c e s.length)) ++ o := by
  obtain ⟨p, hp⟩ := fullB_poly E Ys k c e
  refine ⟨p, fun s o => ?_⟩
  obtain ⟨v, S, h1, h2⟩ := full_run E Ys acc ι sep k c e s o
  exact ⟨v, S, h1.mono (hp _).le, h2⟩

end PvsNP.Pre
