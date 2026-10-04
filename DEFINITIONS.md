# DEFINITIONS.md — the exact formal target

Source of truth: `LeanMillenniumPrizeProblems` at commit
`603053dc267cf3efe422f438eb78098c0ececd6f` (2026-09-10), toolchain `leanprover/lean4:v4.31.0`,
Mathlib `v4.31.0`. File: `Problems/PVersusNP/Millennium.lean`.
This commit is **after** the September 2026 soundness fix
(`1fdee4b`, 2026-09-07, "Fix statement soundness across problems"), which replaced arbitrary
encoded certificate types by strings over a finite alphabet.

## Target

```lean
theorem p_eq_np : Millennium.ClayPVersusNP
-- ClayPVersusNP := ClayPVersusNP.Formulations.ClassEquality
-- ClassEquality :=
--   ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet] (L : Language (List alphabet)),
--     InPolynomialTime (fin_encoding_string alphabet) L ↔
--     InNondeterministicPolynomialTime (fin_encoding_string alphabet) L
```

Both directions are required: the proof must also supply `P ⊆ NP` **unconditionally**.

## Alphabet and strings

* `Σ` = any `alphabet : Type` with `[Fintype alphabet] [Nontrivial alphabet]` (finite, ≥ 2
  symbols), matching Cook ("finite alphabet with at least two elements").
* `Σ*` = `List alphabet`. `Language α := α → Prop`.
* Input encoding: `fin_encoding_string alphabet` = identity (`encode = id`, `Γ = alphabet`).
  So `|w|` = `w.length`.

## Machine model (Mathlib `Turing.FinTM2`, multi-stack machine)

* `K` finite, decidable-eq set of stacks; input stack `k₀`, output stack `k₁` (may coincide).
* Stack alphabets `Γ : K → Type`; **only `Γ k₀` is required `Fintype`**. (Not a loophole: pushed
  symbols are `f v` for `v : σ` finite and finitely many `push` nodes, so only finitely many
  work symbols are ever reachable; output alphabet is `≃` a finite `Γ`.)
* Finite labels `Λ` (`Fintype`), finite state `σ` (`Fintype`), initial state, `main : Λ`.
* Program `m : Λ → TM2.Stmt Γ Λ σ`, statements `push / peek / pop / load / branch / goto / halt`.
  One **step** executes the whole (finite) statement tree of the current label (`TM2.stepAux`),
  i.e. O(1) stack operations per step. `step` on a halted config (`l = none`) returns `none`.
* `initList tm s`: label `main`, state `initialState`, `s` on `k₀`, every other stack empty.
* `haltList tm s`: label `none`, state **`initialState`**, `s` on `k₁`, every other stack
  **empty**. (Machines must clean up and reset their state before halting.)
* `TM2OutputsInTime tm l (some l') m` := `EvalsToInTime tm.step (initList tm l)
  (some (haltList tm l')) m`: iterating `step` for some `steps ≤ m` reaches exactly that config.

## Polynomial-time computability

`TM2ComputableInPolyTime ea eb f` (a `Type`, used under `∃`): a `FinTM2` `tm`, alphabet
equivalences `tm.Γ tm.k₀ ≃ αΓ`, `tm.Γ tm.k₁ ≃ βΓ`, `time : Polynomial ℕ`, and for all `a`,
`TM2OutputsInTime tm (map inv (ea a)) (some (map inv (eb (f a)))) (time.eval (ea a).length)`.

## P

```lean
InPolynomialTime ea L := ∃ (f : α → Bool) (_ : TM2ComputableInPolyTime ea.encode
    finEncodingBoolBool.encode f), ∀ a, L a ↔ f a = true
```
Output encoding of `Bool`: `encodeBool b = [b]`. So a decider halts with exactly `[f a]` on
the output stack. Time bound polynomial in `|w|`. Cook uses single-tape TMs with
`T_M(n) ≤ n^k + k`; multi-stack ↔ single-tape is a polynomial simulation (Cook notes P is
robust across such models), so the class is the standard P.

## Pair encoding (`w#y`)

`pair_encoding ea eb`: alphabet `Sum ea.Γ (Option eb.Γ)`; `encode (w, y) =
map inl (ea w) ++ inr none :: map (inr ∘ some) (eb y)`. `inr none` is the separator `#`.
Length `|w| + 1 + |y|`.

## NP (verifier form)

```lean
InNondeterministicPolynomialTime ea L :=
  ∃ (Γ₁ : Type) (_ : Fintype Γ₁) (R : α → List Γ₁ → Prop) (k : ℕ),
    InPolynomialTime (pair_encoding ea (fin_encoding_string Γ₁)) (fun p => R p.1 p.2) ∧
    ∀ a, L a ↔ ∃ y : List Γ₁, y.length ≤ (ea.encode a).length ^ k ∧ R a y
```
* Verifier: a polynomial-time decider for `L_R = {w#y}` over **all** pairs `(w, y)`, time
  polynomial in `|w| + 1 + |y|`.
* Certificate bound `|y| ≤ |w|^k` (Lean `0^0 = 1`). Matches Cook exactly.
* `Γ₁` may be empty (only restricts; harmless).

## Reductions / completeness

* `PolynomialTimeReducible ea eb L₁ L₂ := ∃ f (_ : TM2ComputableInPolyTime ea.encode
  eb.encode f), ∀ a, L₁ a ↔ L₂ (f a)`.
* `NondeterministicPolynomialTimeComplete ea L := InNP ea L ∧ ∀ {β} (eb : FinEncoding β) L',
  InNP eb L' → PolynomialTimeReducible eb ea L' L`.
  NB: hardness quantifies over **arbitrary** `FinEncoding`s `eb`, not just string alphabets.
  For Cook–Levin we only need the string case if we go through
  `ClayPVersusNP.nondeterministic_polynomial_time_complete_in_polynomial_time`, which requires
  the full (all-encodings) completeness — see "Gap analysis" below.

## Faithfulness verdict (Phase 0 read-through, not yet red-teamed)

No statement bug found. Checked against Cook's Clay PDF (pp. 1–2): alphabet ≥ 2 symbols,
checking relation `L_R ∈ P` over `Σ ∪ Σ₁ ∪ {#}`, bound `|y| ≤ |w|^k`, P via polynomial-time
deterministic machines. Points examined and judged harmless:
1. Non-finite work-stack alphabets — unreachable symbols only (argument above).
2. Noncomputable Lean functions in transition tables — all tables are functions on finite
   types, hence finite.
3. `haltList` demands empty work stacks and reset state — restrictive, not permissive
   (costs O(time) cleanup).
4. `ClayPVersusNP` is not an `P ∨ ¬P` aggregate (repo explicitly avoids that).
A dedicated Lean red-team (Phase 6) is still owed.

## What already exists (plan parts (a)–(c))

| Part | Status in repo/Mathlib | Blocking hypothesis |
|---|---|---|
| (a) `P ⊆ NP` | `PolynomialTimeContainedInNondeterministicPolynomialTime.of_turing_machine_composition` (+ verified linear-time left-projection machine) | `PolynomialTimeComputableComposition` |
| (b) P closed under `≤ₚ` | `PolynomialTimeReducible.source_in_p` | `PolynomialTimeComputableComposition` |
| NP-complete ∈ P ⇒ `ClayPVersusNP` | `ClayPVersusNP.nondeterministic_polynomial_time_complete_in_polynomial_time` | `PolynomialTimeComputableComposition` |
| composition closure | **absent**: Mathlib has only `proof_wanted TM2ComputableInPolyTime.comp` (`Computable.lean:284`) | — |
| (c) Cook–Levin | **absent**: no SAT/CNF language, no NP-completeness proof anywhere | — |
| (d) SAT ∈ P | open problem | — |

## Gap analysis

Everything reduces to three lemmas:

1. `comp : ClayPVersusNP.Support.PolynomialTimeComputableComposition` — known-true
   engineering (disjoint-union machine: run `f`, transfer `k₁_f → k₀_g` twice to preserve
   order, run `g`; output length ≤ |input| + c·p(n) since each step pushes ≤ c symbols; time
   bound `p + O(n + c·p) + q ∘ (X + c·p)`). Unlocks (a) and (b).
2. `cook_levin : NondeterministicPolynomialTimeComplete (fin_encoding_string A) SAT` for some
   concrete SAT encoding over a ≥2-symbol alphabet — known-true but large (a TM2-configuration
   tableau). Note hardness must hold for NP languages under **any** `FinEncoding`.
3. `sat_in_p : InPolynomialTime (fin_encoding_string A) SAT` — **the open problem**, kept as
   one named lemma.

Then `p_eq_np := ClayPVersusNP.nondeterministic_polynomial_time_complete_in_polynomial_time
comp cook_levin sat_in_p`.
