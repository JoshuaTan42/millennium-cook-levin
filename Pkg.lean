import Pre

/-!
# Block A, items 3–4: halting cleanup and packaging

Status: **not a lakefile root** (proposed); checked with `lake env lean Pkg.lean` (its import `Pre` is a
root). See NOTES.md, "BLOCK A, ITEMS 3–4".

`Pre.full_run` stops at the host's `fin` label with the formula on the output stack, but
`TM2OutputsInTime` needs the run to end in exactly `haltList` (label `none`, state `false`, every
other stack empty).

* **[GROW]** generic stack growth for any `FinTM2`: `run_runI`, `run_height` (reusing
  `Sit.runI_height`, i.e. `Sit.stepI_height`).
* **[DRAIN]** a generic drain phase: `xfer_drain` (pop any contents), `drainS`, `drain_run`.
* **[GLUE]** the composed machine `gprog`/`gTM` (full machine relabelled, `fin` redirected to the
  drain), `g_run`: initial configuration to `haltList (encodeCNF (Phi …))`, no hypotheses.
* **[PKG]** `g_outputs` (`TM2OutputsInTime` within one polynomial) and `gComp`
  (`TM2ComputableInPolyTime ea (fin_encoding_string Bool).encode …`), still parametric in the
  verifier data (chosen in item 2).
-/

set_option autoImplicit false

namespace PvsNP.Pkg

open PvsNP.Prog PvsNP.SATDef PvsNP.Emb PvsNP.Pre Turing Function

/-! ## [GROW] Generic stack growth -/

section Grow

open PvsNP.Sit

/-- A real run is the idle-extended run. -/
theorem run_runI {M : FinTM2} (c : M.Cfg) :
    ∀ (n : ℕ) (d : M.Cfg), Run M.m n c d → runI M c n = d := by
  intro n
  induction n with
  | zero =>
      intro d h
      have h' : some c = some d := h
      exact Option.some.inj h'
  | succ n ih =>
      intro d h
      unfold Run at h
      rw [iterate_succ_apply'] at h
      cases he : (flip bind (TM2.step M.m))^[n] (some c) with
      | none => rw [he] at h; simp [flip] at h
      | some e =>
          rw [he] at h
          have h' : TM2.step M.m e = some d := h
          show stepI M (runI M c n) = d
          rw [ih e he, stepI, h']
          rfl

/-- **Generic stack growth**: `n` steps of any `FinTM2` add at most `n · depth M` to a stack. -/
theorem run_height {M : FinTM2} {n : ℕ} {c d : M.Cfg} (h : Run M.m n c d) (k : M.K) :
    (d.stk k).length ≤ (c.stk k).length + n * depth M := by
  rw [← run_runI c n d h]
  exact runI_height c k n

end Grow

/-! ## [DRAIN] A generic drain phase -/

section Drain

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} [Flag σ]
  {M : Λ → TM2.Stmt Γ Λ σ}

/-- `xfer k []` empties stack `k` whatever it holds, in `|S k| + 1` steps. -/
theorem xfer_drain {self next : Λ} {k : K} (hp : M self = xfer k [] self next) :
    ∀ (l : List (Γ k)) (v : σ) (S : ∀ k, List (Γ k)), S k = l →
      Run M (l.length + 1) ⟨some self, v, S⟩ ⟨some next, Flag.tag false, update S k []⟩ := by
  intro l
  induction l with
  | nil =>
      intro v S hS
      have hu : update S k [] = S := by rw [← hS, update_eq_self]
      refine Run.single ?_
      simp only [hp, xfer, TM2.stepAux, hS, List.head?_nil, Option.isSome_none, List.tail_nil,
        Flag.untag_tag, cond_false, hu]
  | cons x l ih =>
      intro v S hS
      have hstep : TM2.step M ⟨some self, v, S⟩ =
          some ⟨some self, Flag.tag true, update S k l⟩ := by
        simp only [TM2.step, hp, xfer, TM2.stepAux, hS, List.head?_cons, Option.isSome_some,
          List.tail_cons, Flag.untag_tag, cond_true, pushAll, List.foldr_nil]
      have key := Run.head hstep (ih (Flag.tag true) (update S k l) (by simp))
      rw [update_idem] at key
      exact key.of_eq (by simp)

/-- The drain program: stage `i < |ks|` empties `ks[i]`; stage `|ks|` resets the state and halts. -/
def drainS (ks : List K) (lab : ℕ → Λ) (i : ℕ) : TM2.Stmt Γ Λ σ :=
  match ks[i]? with
  | some k => xfer k [] (lab i) (lab (i + 1))
  | none => .load (fun _ => Flag.tag false) .halt

/-- Steps of the drain. -/
def drainB (ks : List K) (S : ∀ k, List (Γ k)) : ℕ :=
  (ks.map fun k => (S k).length + 1).sum + 1

/-- **The drain.** Empties every stack of `ks` and halts with state `tag false`. -/
theorem drain_run :
    ∀ (ks : List K) (lab : ℕ → Λ), ks.Nodup → (∀ i ≤ ks.length, M (lab i) = drainS ks lab i) →
      ∀ (v : σ) (S : ∀ k, List (Γ k)),
        Run M (drainB ks S) ⟨some (lab 0), v, S⟩
          ⟨none, Flag.tag false, fun k => if k ∈ ks then [] else S k⟩ := by
  intro ks
  induction ks with
  | nil =>
      intro lab _ hp v S
      refine Run.single ?_
      rw [hp 0 le_rfl]
      simp [drainS, TM2.stepAux]
  | cons k ks ih =>
      intro lab hnd hp v S
      rw [List.nodup_cons] at hnd
      have r1 := xfer_drain (M := M) (self := lab 0) (next := lab 1) (k := k)
        (by rw [hp 0 (by simp)]; rfl) (S k) v S rfl
      have r2 := ih (fun j => lab (j + 1)) hnd.2 (fun i hi => by
        rw [hp (i + 1) (by simp; omega)]; rfl) (Flag.tag false) (update S k [])
      have e1 : drainB ks (update S k []) = drainB ks S := by
        unfold drainB
        congr 2
        refine List.map_congr_left fun k' hk' => ?_
        rw [update_of_ne (fun h : k' = k => hnd.1 (h ▸ hk'))]
      have e2 : (fun k' => if k' ∈ ks then [] else update S k [] k') =
          fun k' => if k' ∈ k :: ks then [] else S k' := by
        funext k'
        by_cases h1 : k' = k
        · subst h1; simp
        · by_cases h2 : k' ∈ ks <;> simp [h1, h2]
      rw [e1, e2] at r2
      exact (r1.trans r2).of_eq (by simp [drainB]; omega)

end Drain

/-! ## [GLUE] The composed machine: full machine, then the drain -/

section Glue

/-- Labels of the composed machine: the full machine's, and the drain stages `0..n`. -/
inductive DL (Λ : Type) (n : ℕ)
  | f (l : Λ)
  | dr (i : Fin (n + 1))
  deriving DecidableEq, Fintype

/-- Drain stage `j` (clamped to `n`). -/
def dlab {Λ : Type} (n j : ℕ) : DL Λ n := .dr ⟨min j n, by omega⟩

/-- The identity stack embedding (pure relabelling). -/
def idE {K : Type} (Γ : K → Type) : SEmb Γ Γ := ⟨id, injective_id, fun _ => Equiv.refl _⟩

/-- Stacks emptied by the drain: every stack except the output. -/
noncomputable def dks : List FK := (Finset.univ.erase (FK.h .out)).toList

theorem mem_dks (q : FK) : q ∈ dks ↔ q ≠ FK.h .out := by simp [dks]

theorem dks_nodup : dks.Nodup := Finset.nodup_toList _

/-- After the drain only the output stack survives. -/
theorem drained {Γ : FK → Type} (T : ∀ k, List (Γ k)) :
    (fun q => if q ∈ dks then [] else T q) = fun q => if q = FK.h .out then T q else [] := by
  funext q
  by_cases hq : q = FK.h .out
  · rw [if_pos hq, if_neg (by rw [mem_dks]; exact not_not.2 hq)]
  · rw [if_neg hq, if_pos ((mem_dks q).2 hq)]

variable {g r : ℕ} {Λ : Type} [DecidableEq Λ]

/-- **The composed program**: the program `P` relabelled, except that its halting label `fin`
jumps to the drain. -/
noncomputable def gprog (P : Λ → TM2.Stmt (FΓ g r) Λ Bool) (fin : Λ) :
    DL Λ dks.length → TM2.Stmt (FΓ g r) (DL Λ dks.length) Bool
  | .f l => if l = fin then .goto (fun _ => dlab _ 0) else mapS (idE _) DL.f (P l)
  | .dr i => drainS dks (dlab _) i.val

theorem embeds_g {P : Λ → TM2.Stmt (FΓ g r) Λ Bool} {fin : Λ} (hfin : P fin = .halt) :
    Embeds (idE (FΓ g r)) DL.f P (gprog P fin) := by
  intro l
  by_cases hl : l = fin
  · exact Or.inr (hl ▸ hfin)
  · exact Or.inl (by simp only [gprog, if_neg hl])

/-- Composed run: `P`'s run to `fin`, one jump, the drain. -/
theorem g_run_gen {P : Λ → TM2.Stmt (FΓ g r) Λ Bool} {fin : Λ} (hfin : P fin = .halt)
    {B : ℕ} {l : Λ} {v v' : Bool} {S T : ∀ k, List (FΓ g r k)}
    (h : RunLe P B ⟨some l, v, S⟩ ⟨some fin, v', T⟩) :
    RunLe (gprog P fin) (B + 1 + drainB dks T) ⟨some (.f l), v, S⟩
      ⟨none, false, fun k => if k ∈ dks then [] else T k⟩ := by
  obtain ⟨T', r1, a1, -⟩ := runLe_embed (E := idE (FΓ g r)) DL.f (embeds_g hfin) h
    (S' := S) (fun _ => (List.map_id _).symm)
  have hT : T' = T := funext fun k => (a1 k).trans (List.map_id _)
  subst hT
  have r2 : Run (gprog P fin) 1 ⟨some (.f fin), v', T'⟩ ⟨some (dlab _ 0), v', T'⟩ :=
    Run.single (by simp [gprog, TM2.stepAux])
  have r3 := drain_run (M := gprog P fin) dks (dlab _) dks_nodup
    (fun i hi => by simp [gprog, dlab, min_eq_left hi]) v' T'
  exact (r1.trans (r2.le le_rfl)).trans (r3.le le_rfl)

/-- Drain steps from a uniform height bound. -/
theorem drainB_le {T : ∀ k, List (FΓ g r k)} {h : ℕ} (hT : ∀ k, (T k).length ≤ h) :
    drainB dks T ≤ dks.length * (h + 1) + 1 := by
  unfold drainB
  have := List.sum_le_card_nsmul (dks.map fun k => (T k).length + 1) (h + 1) (by
    intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact Nat.add_le_add_right (hT k) 1)
  simp only [List.length_map, smul_eq_mul] at this
  omega

end Glue

/-! ## [REAL] The composed machine on the real generators -/

section Real

open PvsNP.Sit PvsNP.Asm

variable {r : ℕ} {M : FinTM2} (E : Enc M)

theorem fullProg_fin (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k c e : ℕ) : fullProg E Ys acc ι sep k c e (.h .fin) = .halt := rfl

/-- **The reduction machine as a `FinTM2`**: the full machine followed by the drain. -/
noncomputable def gTM (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k c e : ℕ) : FinTM2 where
  K := FK
  k₀ := .raw
  k₁ := .h .out
  Γ := FΓ E.layout.g r
  Λ := DL (FL _) dks.length
  main := .f .rd
  σ := Bool
  initialState := false
  m := gprog (fullProg E Ys acc ι sep k c e) (.h .fin)

/-- The emitted formula for raw input `s`. -/
noncomputable def phiOf (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k c e : ℕ) (s : List (Fin r)) : List Bool :=
  encodeCNF (Phi E (s.map ι ++ [sep]) Ys acc (mOf k s.length) (TOf k c e s.length))

/-- Step bound of the composed machine (`D = depth` of the full machine, a constant). -/
noncomputable def gB (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k c e n : ℕ) : ℕ :=
  fullB E Ys k c e n + 1 +
    (dks.length * (n + fullB E Ys k c e n * depth (fullTM E Ys acc ι sep k c e) + 1) + 1)

theorem initList_g (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k c e : ℕ) (s : List (Fin r)) :
    initList (gTM E Ys acc ι sep k c e) s = ⟨some (.f .rd), false, fst s [] 0 []⟩ := by
  simp only [initList]
  congr 1
  funext q
  rcases q with q | _ | x
  · cases q <;> rfl
  · rfl
  · cases x <;> rfl

theorem haltList_g (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k c e : ℕ) (T : ∀ k, List (FΓ E.layout.g r k)) :
    haltList (gTM E Ys acc ι sep k c e) (T (.h .out)) =
      ⟨none, false, fun q => if q = FK.h .out then T q else []⟩ := by
  simp only [haltList]
  congr 1
  funext q
  rcases q with q | _ | x
  · cases q <;> rfl
  · rfl
  · rfl

/-- **The composed machine, raw input to `haltList`.** From `initList` on the raw input `s`, the
reduction machine halts in exactly `haltList (phiOf s)` within `gB |s|` steps. No hypotheses. -/
theorem g_run (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k c e : ℕ) (s : List (Fin r)) :
    RunLe (gTM E Ys acc ι sep k c e).m (gB E Ys acc ι sep k c e s.length)
      (initList (gTM E Ys acc ι sep k c e) s)
      (haltList (gTM E Ys acc ι sep k c e) (phiOf E Ys acc ι sep k c e s)) := by
  obtain ⟨v, S, ⟨n1, hn1, r1⟩, hout⟩ := full_run E Ys acc ι sep k c e s []
  rw [List.append_nil] at hout
  -- stack heights at the end of the full machine's run (generic growth lemma)
  have hh : ∀ q, (S q).length ≤
      s.length + fullB E Ys k c e s.length * depth (fullTM E Ys acc ι sep k c e) := by
    intro q
    have r1' : Run (fullTM E Ys acc ι sep k c e).m n1 (initList (fullTM E Ys acc ι sep k c e) s)
        ⟨some (.h .fin), v, S⟩ := by rw [initList_full]; exact r1
    have h1 := run_height r1' q
    have h2 : ((initList (fullTM E Ys acc ι sep k c e) s).stk q).length ≤ s.length :=
      initList_height (M := fullTM E Ys acc ι sep k c e) s q
    have h3 := Nat.mul_le_mul_right (depth (fullTM E Ys acc ι sep k c e)) hn1
    exact h1.trans (by omega)
  have hg := g_run_gen (fullProg_fin E Ys acc ι sep k c e) ⟨n1, hn1, r1⟩
  rw [drained] at hg
  rw [initList_g, show phiOf E Ys acc ι sep k c e s = S (.h .out) from hout.symm, haltList_g]
  exact hg.mono (by unfold gB; have := drainB_le hh; omega)

end Real

/-! ## [PKG] `TM2OutputsInTime` and `TM2ComputableInPolyTime` -/

section Pkg

open PvsNP.Sit PvsNP.Asm Millennium

/-- A bounded run from `initList` to `haltList` is a `TM2OutputsInTime` certificate. -/
noncomputable def outputsOfRunLe {tm : FinTM2} {l : List (tm.Γ tm.k₀)} {l' : List (tm.Γ tm.k₁)}
    {B : ℕ} (h : RunLe tm.m B (initList tm l) (haltList tm l')) :
    TM2OutputsInTime tm l (some l') B where
  steps := Classical.choose h
  evals_in_steps := (Classical.choose_spec h).2
  steps_le_m := (Classical.choose_spec h).1

/-- `outputsOfRunLe` up to an equation on the output. -/
noncomputable def outputsOfRunLe' {tm : FinTM2} {l : List (tm.Γ tm.k₀)}
    {l' l'' : List (tm.Γ tm.k₁)} {B : ℕ} (h : RunLe tm.m B (initList tm l) (haltList tm l''))
    (he : l'' = l') : TM2OutputsInTime tm l (some l') B :=
  outputsOfRunLe (he ▸ h)

variable {r : ℕ} {M : FinTM2} (E : Enc M)

theorem gB_poly (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k c e : ℕ) : IsPoly (gB E Ys acc ι sep k c e) := by
  unfold gB
  generalize depth (fullTM E Ys acc ι sep k c e) = D
  generalize (dks : List FK).length = L
  have hf := fullB_poly E Ys k c e
  exact (hf.add (IsPoly.const 1)).add (((IsPoly.const L).mul
    ((IsPoly.id.add (hf.mul (IsPoly.const D))).add (IsPoly.const 1))).add (IsPoly.const 1))

/-- **One polynomial** bounding the composed machine on every input. -/
theorem g_outputs (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k c e : ℕ) :
    ∃ p : Polynomial ℕ, ∀ s : List (Fin r),
      Nonempty (TM2OutputsInTime (gTM E Ys acc ι sep k c e) s
        (some (phiOf E Ys acc ι sep k c e s)) (p.eval s.length)) := by
  obtain ⟨p, hp⟩ := gB_poly E Ys acc ι sep k c e
  exact ⟨p, fun s => ⟨outputsOfRunLe ((g_run E Ys acc ι sep k c e s).mono (hp _).le)⟩⟩

/-- The reduction function on encoded inputs: decode the raw symbols, emit `Phi`. -/
noncomputable def fR {α αΓ : Type} (ea : α → List αΓ) (eqv : Fin r ≃ αΓ)
    (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀) (sep : M.Γ M.k₀)
    (k c e : ℕ) (a : α) : List Bool :=
  phiOf E Ys acc ι sep k c e ((ea a).map eqv.invFun)

/-- **The packaged reduction machine**: `TM2ComputableInPolyTime` from `ea` to the identity
encoding of `List Bool`, computing `fR`. Still parametric in the verifier data. -/
noncomputable def gComp {α αΓ : Type} (ea : α → List αΓ) (eqv : Fin r ≃ αΓ)
    (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀) (sep : M.Γ M.k₀)
    (k c e : ℕ) :
    TM2ComputableInPolyTime ea (fin_encoding_string Bool).encode
      (fR E ea eqv Ys acc ι sep k c e) where
  tm := gTM E Ys acc ι sep k c e
  inputAlphabet := eqv
  outputAlphabet := Equiv.refl Bool
  time := Classical.choose (gB_poly E Ys acc ι sep k c e)
  outputsFun a := outputsOfRunLe' (by
    have h := g_run E Ys acc ι sep k c e ((ea a).map eqv.invFun)
    rw [List.length_map, Classical.choose_spec (gB_poly E Ys acc ι sep k c e)] at h
    exact h) (List.map_id _).symm

end Pkg

end PvsNP.Pkg

/-! # Block A, items 1, 2, 5, 6: closing `cook_levin` (2026-10-05)

* **[POLY]** `eval_le_pow`: every `Polynomial ℕ` is bounded by some `(j + c)^e` (item 2).
* **[ENC]** `encX`: `Enc.ofFinTM2` with the accept symbol added to the effective output alphabet,
  so `phi_iff`'s `hacc` holds unconditionally (`encX_acc`). This replaces item 6's case split.
* **[VER]** items 1–2: the verifier machine, input symbols `ι`, separator, certificate symbols
  `Ys`, accept symbol, and `c, e` with `time ≤ (m + c)^e`.
* **[CORR]** item 5, `v_correct`: `L' a ↔ SAT (fR a)`.
* **[HARD]** `sat_np_hard`, then `PvsNP.cook_levin` (moved here from CookLevin.lean: the
  reduction chain imports CookLevin, so the proof cannot live there; statement unchanged). -/

namespace PvsNP.CL

open PvsNP.SATDef PvsNP.Sit PvsNP.Asm PvsNP.Pre PvsNP.Pkg Turing Millennium Computability

/-! ## [POLY] Every polynomial is bounded by some `(j + c)^e` -/

theorem eval_mono' (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; omega
  | monomial n c =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h n)

theorem pow_weaken {j c e c' e' : ℕ} (hc : 1 ≤ c) (h1 : c ≤ c') (h2 : e ≤ e') :
    (j + c) ^ e ≤ (j + c') ^ e' :=
  (Nat.pow_le_pow_left (by omega) e).trans (Nat.pow_le_pow_right (by omega) h2)

theorem eval_le_pow (p : Polynomial ℕ) : ∃ c e, 1 ≤ c ∧ ∀ j, p.eval j ≤ (j + c) ^ e := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨c1, e1, hc1, h1⟩ := hp
      obtain ⟨c2, e2, hc2, h2⟩ := hq
      refine ⟨c1 + c2, e1 + e2 + 1, by omega, fun j => ?_⟩
      have a1 := (h1 j).trans
        (pow_weaken (j := j) hc1 (Nat.le_add_right c1 c2) (Nat.le_add_right e1 e2))
      have a2 := (h2 j).trans
        (pow_weaken (j := j) hc2 (Nat.le_add_left c2 c1) (Nat.le_add_left e2 e1))
      have h2le : 2 ≤ j + (c1 + c2) := by omega
      rw [Polynomial.eval_add, pow_succ]
      calc p.eval j + q.eval j
          ≤ (j + (c1 + c2)) ^ (e1 + e2) + (j + (c1 + c2)) ^ (e1 + e2) := Nat.add_le_add a1 a2
        _ = (j + (c1 + c2)) ^ (e1 + e2) * 2 := by ring
        _ ≤ (j + (c1 + c2)) ^ (e1 + e2) * (j + (c1 + c2)) := Nat.mul_le_mul_left _ h2le
  | monomial n a =>
      refine ⟨a + 1, n + 1, by omega, fun j => ?_⟩
      rw [Polynomial.eval_monomial, pow_succ]
      calc a * j ^ n ≤ (j + (a + 1)) * (j + (a + 1)) ^ n :=
            Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) n)
        _ = _ := mul_comm _ _

/-! ## [LIST] Pulling a list back through a map -/

theorem pull {α β : Type} (f : α → β) (L : List α) :
    ∀ l : List β, (∀ z ∈ l, z ∈ L.map f) → ∃ l0 : List α, l0.map f = l
  | [], _ => ⟨[], rfl⟩
  | z :: l, h => by
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 (h z (by simp))
      obtain ⟨l0, rfl⟩ := pull f L l (fun w hw => h w (by simp [hw]))
      exact ⟨u :: l0, rfl⟩

/-! ## [ENC] An encoding whose output alphabet contains a chosen accept symbol -/

section Classical

open Classical

/-- `symSet` plus one extra symbol `acc` on the output stack. -/
noncomputable def symSetX (M : FinTM2) (acc : M.Γ M.k₁) (k : M.K) : Finset (M.Γ k) :=
  symSet M k ∪ (if h : M.k₁ = k then {cast (congrArg M.Γ h) acc} else ∅)

theorem acc_mem_symSetX (M : FinTM2) (acc : M.Γ M.k₁) : acc ∈ symSetX M acc M.k₁ := by
  unfold symSetX
  exact Finset.mem_union_right _ (by rw [dif_pos rfl]; exact Finset.mem_singleton_self _)

/-- `Enc.ofFinTM2` with `acc` added to the effective output alphabet. -/
noncomputable def encX (M : FinTM2) (acc : M.Γ M.k₁) : Enc M :=
  letI := M.kFin; letI := M.ΛFin; letI := M.σFin
  { KK := Fintype.card M.K
    kc := fun k => Fintype.equivFin M.K k
    kd := fun n => if h : n < Fintype.card M.K then (Fintype.equivFin M.K).symm ⟨n, h⟩ else M.k₀
    kc_lt := fun k => (Fintype.equivFin M.K k).2
    kd_kc := fun k => by simp
    kc_kd := fun n hn => by simp [hn]
    A0 := Fintype.card (Option M.Λ × M.σ)
    lc := fun x => Fintype.equivFin _ x
    ld := fun c => if h : c < Fintype.card (Option M.Λ × M.σ) then
      (Fintype.equivFin _).symm ⟨c, h⟩ else (none, M.initialState)
    lc_lt := fun x => (Fintype.equivFin _ x).2
    ld_lc := fun x => by rw [dif_pos (Fintype.equivFin _ x).2]; simp
    lc_ld := fun c hc => by rw [dif_pos hc]; simp
    sz := fun k => (symSetX M acc k).card
    dec := fun k i => ((symSetX M acc k).equivFin.symm i).1
    enc := fun k x => if h : x ∈ symSetX M acc k then (symSetX M acc k).equivFin ⟨x, h⟩ + 1 else 0
    enc_dec := fun k i => by simp
    push_mem := fun l k x h => ⟨(symSetX M acc k).equivFin
      ⟨x, Finset.mem_union_left _ (push_mem_symSet M l k x h)⟩, by simp⟩
    input_mem := fun x => ⟨(symSetX M acc M.k₀).equivFin
      ⟨x, Finset.mem_union_left _ (input_mem_symSet M x)⟩, by simp⟩ }

/-- The accept symbol is encodable: `phi_iff`'s `hacc`, unconditionally. -/
theorem encX_acc (M : FinTM2) (acc : M.Γ M.k₁) : ∃ i, (encX M acc).dec M.k₁ i = acc :=
  ⟨(symSetX M acc M.k₁).equivFin ⟨acc, acc_mem_symSetX M acc⟩, by simp [encX]⟩

end Classical

/-! ## [VER] Items 1–2: the verifier's machine and the reduction's parameters -/

section Ver

variable {β Γ₁ : Type} [Fintype Γ₁] {eb : FinEncoding β} {fv : β × List Γ₁ → Bool}
  (V : TM2ComputableInPolyTime (pair_encoding eb (fin_encoding_string Γ₁)).encode
    finEncodingBoolBool.encode fv)

/-- Accept symbol: the verifier's output symbol for `true`. -/
def vacc : V.tm.Γ V.tm.k₁ := V.outputAlphabet.symm true

noncomputable def vE : Enc V.tm := encX V.tm (vacc V)

/-- Raw input alphabet size of `eb`. -/
def vr (eb : FinEncoding β) : ℕ := @Fintype.card eb.Γ eb.ΓFin

noncomputable def veqv (eb : FinEncoding β) : Fin (vr eb) ≃ eb.Γ :=
  (@Fintype.equivFin eb.Γ eb.ΓFin).symm

/-- Input symbol `i` of `w`, as the verifier sees it (left-tagged). -/
noncomputable def vι (i : Fin (vr eb)) : V.tm.Γ V.tm.k₀ :=
  V.inputAlphabet.symm (Sum.inl (veqv eb i) : eb.Γ ⊕ Option Γ₁)

/-- The separator `#`. -/
def vsep : V.tm.Γ V.tm.k₀ := V.inputAlphabet.symm (Sum.inr none : eb.Γ ⊕ Option Γ₁)

/-- Certificate symbol `g`, right-tagged. -/
def vY (g : Γ₁) : V.tm.Γ V.tm.k₀ := V.inputAlphabet.symm (Sum.inr (some g) : eb.Γ ⊕ Option Γ₁)

noncomputable def vYs : List (V.tm.Γ V.tm.k₀) := (Finset.univ : Finset Γ₁).toList.map (vY V)

/-- Item 2: `T = (m + c)^e` dominates the verifier's time polynomial. -/
noncomputable def vc : ℕ := Classical.choose (eval_le_pow V.time)

noncomputable def ve : ℕ := Classical.choose (Classical.choose_spec (eval_le_pow V.time))

theorem v_time (j : ℕ) : V.time.eval j ≤ (j + vc V) ^ ve V :=
  (Classical.choose_spec (Classical.choose_spec (eval_le_pow V.time))).2 j

/-- The verifier's input on `(a, y)` is `x ++ (y mapped)`, `x` = tagged `w` then `#`. -/
theorem v_input (a : β) (y : List Γ₁) :
    List.map V.inputAlphabet.invFun ((pair_encoding eb (fin_encoding_string Γ₁)).encode (a, y)) =
      ((eb.encode a).map (veqv eb).invFun).map (vι V) ++ [vsep V] ++ y.map (vY V) := by
  rw [pair_encoding.encode_eq]
  rw [List.append_assoc, List.singleton_append]
  erw [List.map_append, List.map_cons, List.map_map, List.map_map]
  congr 1
  rw [List.map_map]
  refine List.map_congr_left fun g _ => ?_
  simp [vι, veqv]
  rfl

/-- Determinism link: from row `T` on, the verifier's run on `(a, y)` is its output. -/
theorem v_run (a : β) (y : List Γ₁) {T : ℕ}
    (hT : V.time.eval ((eb.encode a).length + 1 + y.length) ≤ T) :
    runI V.tm (initList V.tm (((eb.encode a).map (veqv eb).invFun).map (vι V) ++ [vsep V] ++
      y.map (vY V))) T = haltList V.tm [V.outputAlphabet.symm (fv (a, y))] := by
  have h := V.outputsFun (a, y)
  rw [v_input] at h
  have hl : ((pair_encoding eb (fin_encoding_string Γ₁)).encode (a, y)).length =
      (eb.encode a).length + 1 + y.length := by
    rw [pair_encoding.length_eq]; rfl
  rw [hl] at h
  exact runI_haltList V.tm _ _ h hT

/-! ## [CORR] Item 5: correctness -/

/-- **Item 5.** `L' a ↔ SAT (fR a)` for the parameters of items 1–2. -/
theorem v_correct {R : β → List Γ₁ → Prop} {k : ℕ} {L' : Language β}
    (hfv : ∀ p : β × List Γ₁, R p.1 p.2 ↔ fv p = true)
    (hL : ∀ a, L' a ↔ ∃ y : List Γ₁, y.length ≤ (eb.encode a).length ^ k ∧ R a y) (a : β) :
    L' a ↔ SAT (fR (vE V) eb.encode (veqv eb) (vYs V) (vacc V) (vι V) (vsep V) k (vc V) (ve V) a) := by
  set n := (eb.encode a).length with hn
  set s := (eb.encode a).map (veqv eb).invFun with hs
  have hsl : s.length = n := by rw [hs, List.length_map]
  have hx : (s.map (vι V) ++ [vsep V]).length ≤ mOf k s.length := by
    simp only [List.length_append, List.length_map, List.length_singleton, mOf]; omega
  show L' a ↔ ∃ asg, cnfSat (decodeCNF (encodeCNF (Phi (vE V) (s.map (vι V) ++ [vsep V]) (vYs V)
    (vacc V) (mOf k s.length) (TOf k (vc V) (ve V) s.length)))) asg
  rw [decodeCNF_encodeCNF, phi_iff (vE V) hx (encX_acc _ _), hL, hsl]
  -- the time bound: any certificate within the length cap runs to completion by row `T`
  have hT : ∀ y : List Γ₁, n + 1 + y.length ≤ mOf k n →
      V.time.eval (n + 1 + y.length) ≤ TOf k (vc V) (ve V) n := fun y hy =>
    (eval_mono' _ hy).trans (v_time V _)
  -- acceptance at row `T` is exactly `fv (a, y) = true`
  have hacc : ∀ y : List Γ₁, n + 1 + y.length ≤ mOf k n →
      (Accepts V.tm (runI V.tm (initList V.tm (s.map (vι V) ++ [vsep V] ++ y.map (vY V)))
        (TOf k (vc V) (ve V) n)) (vacc V) ↔ fv (a, y) = true) := by
    intro y hy
    rw [hs, v_run V a y (hT y hy), accepts_haltList]
    simp [vacc]
    exact Iff.rfl
  constructor
  · rintro ⟨y, hy, hR⟩
    rw [← hn] at hy
    have hyl : n + 1 + y.length ≤ mOf k n := by unfold mOf; omega
    refine ⟨y.map (vY V), fun z hz => ?_, ?_, (hacc y hyl).2 ((hfv (a, y)).1 hR)⟩
    · obtain ⟨g, -, rfl⟩ := List.mem_map.1 hz
      exact List.mem_map.2 ⟨g, Finset.mem_toList.2 (Finset.mem_univ g), rfl⟩
    · simp only [List.length_append, List.length_map, List.length_singleton]; rw [hsl]; exact hyl
  · rintro ⟨y', hY, hlen, hA⟩
    obtain ⟨y, rfl⟩ := pull (vY V) _ y' hY
    have hyl : n + 1 + y.length ≤ mOf k n := by
      simp only [List.length_append, List.length_map, List.length_singleton] at hlen
      rw [hsl] at hlen; exact hlen
    refine ⟨y, by rw [← hn]; unfold mOf at hyl; omega, (hfv (a, y)).2 ((hacc y hyl).1 ?_)⟩
    exact hA

end Ver

/-! ## [HARD] NP-hardness of `SAT` -/

theorem sat_np_hard {β : Type} (eb : FinEncoding β) (L' : Language β)
    (hL : InNondeterministicPolynomialTime eb L') :
    PolynomialTimeReducible eb (fin_encoding_string Bool) L' SAT := by
  obtain ⟨Γ₁, hΓ, R, k, ⟨fv, V, hfv⟩, hLR⟩ := hL
  exact ⟨_, gComp (vE V) eb.encode (veqv eb) (vYs V) (vacc V) (vι V) (vsep V) k (vc V) (ve V),
    v_correct V hfv hLR⟩

end PvsNP.CL

namespace PvsNP

open Millennium

/-- Cook–Levin: `SAT` is NP-complete. Membership is `sat_in_np` (CookLevin.lean); hardness is
`CL.sat_np_hard`. (Statement identical to the former placeholder declaration in CookLevin.lean.) -/
theorem cook_levin : NondeterministicPolynomialTimeComplete (fin_encoding_string Bool) SAT :=
  ⟨sat_in_np, fun eb L' hL => CL.sat_np_hard eb L' hL⟩

end PvsNP
