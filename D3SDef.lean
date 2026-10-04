import D3Shift

/-!
# D3, fourth family: situation definitions `S[t,i]` (EXPLORATORY)

Status: exploratory, **not a lakefile root**; imports `D3Shift` (a root since 2026-09-29; check
with `lake env lean D3SDef.lean`). See NOTES.md, "SITUATION VARIABLES: DESIGN FIXED".

The situation variable of step `t` lives in the situation block of row `t + 1`:
`S[t,i] = xIdx H (t+1) (sa i)`. Its defining clauses (one direction of Tseitin: "row `t` is in
situation `i`" ⇒ `S[t,i]`) are, for `t < T`, `i < N`,

  `¬X[t, la i] ∨ ⋁_{k < KK, j < d} ¬C[t, k, j, wa i k j] ∨ S[t,i]`.

The family is stated here independently (`sdFamily`) and then shown to be **literally** the D3Fam
family with the next-code table `na := sa` (`sdFamily_eq`), because D3Fam's head literal
`X[t+1, na i]` sits exactly where `S[t,i]` does. The generator, its finite labels and its
polynomial time bound are therefore D3Fam's (`sd_time`, `sdTM`). `shLits_S`/`ovLits_S`/`pfLits_S`
record, in Lean, that the shift family's `S` literal (all three clause kinds) is this same variable.
-/

namespace PvsNP.D3SD

open PvsNP.Prog PvsNP.SATDef
open PvsNP.D3Fam (Layout denseClause Inc)

/-! ## The family (pure specification, stated without reference to D3Fam's `litPos`) -/

section Spec

variable (L : Layout) (la sa : ℕ → ℕ) (wa : ℕ → ℕ → ℕ → ℕ)

/-- The situation variable `S[t,i]` of step `t`: slot `sa i` of row `t + 1`. -/
def sIdx (H t i : ℕ) : ℕ := L.xIdx H (t + 1) (sa i)

/-- The (negated) window literals of situation `i` at time `t`, stacks then depths. -/
def winLits (H t i : ℕ) : List (ℕ × Bool) :=
  (List.range L.KK).flatMap fun k =>
    (List.range L.d).map fun j => (L.cIdx H t k j (wa i k j), false)

/-- Defining clause of `S[t,i]`: `¬X[t, la i] ∨ ⋁ ¬C[t,k,j,wa i k j] ∨ S[t,i]`. -/
def sdLits (H t i : ℕ) : List (ℕ × Bool) :=
  (L.xIdx H t (la i), false) :: (winLits L wa H t i ++ [(sIdx L sa H t i, true)])

/-- **The family**: clauses ordered by time, then situation. -/
def sdFamily (T H N : ℕ) : CNF :=
  (List.range T).flatMap fun t =>
    (List.range N).map fun i => denseClause (L.numVars T H) (sdLits L la sa wa H t i)

end Spec

/-! ## It is the D3Fam family with `na := sa` -/

/-- Enumerating `k < K`, `j < d` lexicographically is enumerating `n < K·d` by `(n / d, n % d)`. -/
theorem flatMap_range_divmod {α : Type} (f : ℕ → ℕ → α) (K d : ℕ) :
    (List.range K).flatMap (fun k => (List.range d).map (f k)) =
      (List.range (K * d)).map (fun n => f (n / d) (n % d)) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add, List.map_append,
        List.map_map, List.flatMap_singleton]
      congr 1
      refine List.map_congr_left fun j hj => ?_
      rw [List.mem_range] at hj
      have hd : 0 < d := by omega
      have h1 : (K * d + j) / d = K := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hj, Nat.zero_add]
      have h2 : (K * d + j) % d = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
      simp [h1, h2]

variable {L : Layout} {la sa : ℕ → ℕ} {wa : ℕ → ℕ → ℕ → ℕ}

theorem sdLits_eq (H t i : ℕ) : sdLits L la sa wa H t i = D3Fam.lits L la sa wa H t i := by
  unfold sdLits winLits D3Fam.lits Layout.nLits
  rw [flatMap_range_divmod (fun k j => (L.cIdx H t k j (wa i k j), false)),
    show L.KK * L.d + 2 = (L.KK * L.d + 1) + 1 from rfl, List.range_succ, List.range_succ_eq_map,
    List.map_append, List.map_cons, List.map_map, List.cons_append]
  congr 2
  · refine List.map_congr_left fun n hn => ?_
    rw [List.mem_range] at hn
    simp only [Function.comp, D3Fam.litPos, Nat.add_one_ne_zero, if_false,
      show n + 1 ≤ L.KK * L.d by omega, if_true, Nat.add_sub_cancel]
    simp
    omega
  · simp [D3Fam.litPos, sIdx]

/-- **The S-definition family is D3Fam's family with the next-code table `sa`.** -/
theorem sdFamily_eq (T H N : ℕ) :
    sdFamily L la sa wa T H N = D3Fam.family L la sa wa T H N := by
  unfold sdFamily D3Fam.family
  simp only [sdLits_eq]

/-- Sortedness and range of the defining clause (so its dense encoding is well-formed). -/
theorem sd_sorted {T H t i : ℕ} (ht : t < T) (hwf : D3Fam.WF L la sa wa H i) :
    Inc 0 (sdLits L la sa wa H t i) (L.numVars T H) := by
  rw [sdLits_eq]; exact D3Fam.lits_inc ht hwf

/-! ## Generator, finite labels, time bound: inherited -/

/-- The S-definition generator as a genuine `FinTM2` (finite labels `GL N nLits`). -/
def sdTM (L : Layout) (la sa : ℕ → ℕ) (wa : ℕ → ℕ → ℕ → ℕ) (N : ℕ) : Turing.FinTM2 :=
  D3Fam.genTM L la sa wa N

/-- **Time-bound target.** Started on `T`, `H` (unary) with empty scratch counters, the generator
reaches `done` within `genC L N · (T + H + 1)^5` steps with the S-definition family's encoding
prepended to the output. -/
theorem sd_time {N : ℕ} (T H : ℕ) (hwf : ∀ i < N, D3Fam.WF L la sa wa H i) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (D3Fam.GΓ k)),
      RunLe (D3Fam.prog L la sa wa N) (D3Fam.genC L N * (T + H + 1) ^ 5)
        ⟨some (.pre .eg), false, D3Fam.st (D3Fam.initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (sdFamily L la sa wa T H N) ++ o := by
  rw [sdFamily_eq]
  exact D3Fam.gen_time T H hwf o

/-! ## The shift family uses the same variable -/

theorem shLits_S {pl cn : ℕ → ℕ → ℕ} (H t i k u x : ℕ) :
    D3SH.shLits L sa pl cn H t i k u x =
      [(L.cIdx H t k (u + cn i k) x, false), (sIdx L sa H t i, false),
        (L.cIdx H (t + 1) k (u + pl i k) x, true)] := rfl

theorem ovLits_S {pl cn : ℕ → ℕ → ℕ} (H t i k r : ℕ) :
    D3SH.ovLits L sa pl cn H t i k r =
      [(sIdx L sa H t i, false), (L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0, true)] := rfl

theorem pfLits_S {pu : ℕ → ℕ → ℕ → ℕ} (H t i k j : ℕ) :
    D3SH.pfLits L sa pu H t i k j =
      [(sIdx L sa H t i, false), (L.cIdx H (t + 1) k j (pu i k j), true)] := rfl

/-- `S[t,i]` lies in row `t + 1`'s label/state/situation block, below every cell of that row. -/
theorem sIdx_block {H t i : ℕ} (hs : sa i < L.A) :
    (t + 1) * L.rowW H ≤ sIdx L sa H t i ∧ sIdx L sa H t i < (t + 1) * L.rowW H + L.A := by
  unfold sIdx Layout.xIdx; omega

end PvsNP.D3SD
