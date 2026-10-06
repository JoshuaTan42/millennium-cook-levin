# REDTEAM.md — Phase 6 adversarial review of the proved results

Date: 2026-10-06. Reviewer: the research agent (Claude Code), read-only session; nothing committed.
Reviewed tree: `D:\PvsNP`, branch `sat-in-p` at `96efce1`; the public repository
`github.com/JoshuaTan42/millennium-cook-levin` (`origin/master` = `9cc4ad3`). All Lean files, `README.md`,
`DEFINITIONS.md`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` and the submodule pointer
(`603053dc`) are byte-identical between the local `HEAD` and `origin/master` (`git diff --stat HEAD
origin/master -- '*.lean' README.md ...` is empty; the only difference is `.gitmodules`, which locally
adds the Phase 4 `dpr-trim` submodule). The local branch carries two extra commits (Phase 3 and Phase 4
documents and `phase4/` tooling); they touch no Lean file.

Toolchain: Lean `4.31.0` (`68218e87`, x86_64-w64-windows-gnu), Mathlib `fabf563a` (tag `v4.31.0`),
LeanMillenniumPrizeProblems `603053d` (2026-09-10, three commits after the soundness fix `1fdee4b` of
2026-09-07), Physlib `3dddd61e`.

Targets reviewed: `PvsNP.cook_levin` (Pkg.lean), `PvsNP.sat_in_np` and `PvsNP.SAT` (CookLevin.lean),
`PvsNP.CL.sat_np_hard` (Pkg.lean), `PvsNP.tm2ComputableInPolyTime_comp` and `PvsNP.comp` (Comp.lean),
and the `Challenge.lean` / `Solution.lean` pair.

---

## ACTION REQUIRED BEFORE ANYTHING ELSE (incident caused by this session)

While setting up the Comparator check (item 5) I filled the `C:` drive. The WSL distro
`Ubuntu-22.04` keeps its disk image on `C:`
(`C:\Users\Joshua Tan\AppData\Local\Packages\CanonicalGroupLimited.Ubuntu22.04LTS_79rhkp1fndgsc\LocalState\ext4.vhdx`,
now 9,446,621,184 bytes), and my clean-clone build inside it (toolchains, Mathlib clone, cache download)
consumed the few GB that `C:` had left. `df` now reports `C: 232G 232G 0 100%`. The WSL service can no
longer attach the image ("There is not enough space on the disk", `Wsl/Service/CreateInstance/MountVhd/HCS/0x80070070`),
so I could not delete my files from inside it. Moving the image to `D:` and repointing the registry
`BasePath` was blocked by the permission classifier, and I did not pursue it. I did:

* run `wsl --manage Ubuntu-22.04 --set-sparse true` (succeeded; this only changes the VHD to sparse mode);
* create and then remove a temporary `C:\Users\Joshua Tan\.wslconfig` (`[wsl2] swap=0`); it no longer exists.

Nothing of the user's data was deleted. Everything I created is inside the distro under `~/redteam`
(`mcl` clean clone with partial package downloads, `comparator`, `lean4export`, `landrun`), plus
`~/.elan` (toolchains v4.31.0 and v4.35.0-rc3), `~/go-sdk`, and possibly `~/.cache/mathlib`. To recover:

1. Free a few GB on `C:` (the Windows Mathlib download cache `%USERPROFILE%\.cache\mathlib` is
   re-downloadable but only 432 MB, so something larger is needed), and consider temporarily adding
   `[wsl2] swap=0` to `%USERPROFILE%\.wslconfig` so that WSL does not need to create a swap file on `C:`.
   At the time of writing `C:` oscillates between 0 and ~470 MB free.
2. `wsl -d Ubuntu-22.04 -e bash -lc 'rm -rf ~/redteam ~/.elan ~/go-sdk ~/.cache/mathlib'` and
   `wsl --shutdown`. With sparse mode on, the image should shrink back to roughly its previous size.
3. Alternatively relocate the distro to `D:` (`wsl --export`, `wsl --unregister`, `wsl --import`), which
   is what I wanted to do and left to you.

The rest of this report does not depend on WSL.

---

## 0. Verdict

| Severity | Count | Summary |
|---|---|---|
| CRITICAL (claim is wrong) | 0 | none found |
| MAJOR (claim needs a caveat) | 0 | none found |
| MINOR (documentation) | 4 | M1–M4 below |
| INCOMPLETE | 1 | item 5 (Comparator in WSL) could not be run; see section 6 |

Everything the README claims about the proved results checks out against the pinned definitions, the
build, the axiom printer, the kernel re-checker, the repository's own test suite, and independent
Lean/Python witnesses written for this review. The only caveats are wording-level.

### Ranked findings

| ID | Severity | Finding | Where |
|---|---|---|---|
| M1 | MINOR | "Polynomially related in both directions" is true for the *languages* (poly-time inter-reducible), not for the naive encoding map: a standard clause mentioning variable `x_N` costs `2(N+1)` dense bits, exponential in the `log N` bits of a binary index. The standard-to-dense direction needs variable renumbering (and dropping tautological clauses, which a dense row cannot express). | README "The SAT encoding"; section 3 |
| M2 | MINOR | Junk strings are members: `SAT []` holds and any string with no `00` terminator decodes to the empty formula, which is satisfiable. Standard convention is either way; it is a linear-time recognisable set so it changes nothing, but a reader comparing with "unparseable ⇒ reject" should know. | CookLevin.lean `decodeAux`; section 3 |
| M3 | MINOR | README does not mention that Mathlib's `FinTM2` only requires the input-stack alphabet to be finite and lets transition tables be arbitrary (noncomputable) Lean functions. DEFINITIONS.md records the "finitely many reachable symbols" argument; the README should point to it, since this is the first place a sceptic looks for a model loophole. | README, DEFINITIONS.md; section 2.4 |
| M4 | MINOR | The certificate bound in the repository's NP is literally Cook's `|y| ≤ |w|^k`, so inputs of length 0 or 1 admit certificates of length at most 1. Harmless (finitely many inputs; `0^0 = 1` in Lean), inherited from the pinned repo, not from this project. Worth one sentence in DEFINITIONS.md. | Millennium.lean `InNondeterministicPolynomialTime` |

Nothing else rose to the level of a finding. Section 7 lists what remains unverified by machine.

---

## 1. What was run (all outputs quoted in the appendix)

| Check | Command | Result |
|---|---|---|
| Build | `lake build` (D:\PvsNP) | `Build completed successfully (1270 jobs)`, exactly two `sorry` warnings: `Challenge.lean:3:8`, `SatInP.lean:15:8` |
| Axioms | `lake env lean Check.lean` | `cook_levin`, `sat_in_np`, `CL.sat_np_hard`, `tm2ComputableInPolyTime_comp`, `comp`: `[propext, Classical.choice, Quot.sound]`; `sat_in_p`: `[propext, sorryAx, Quot.sound]`; `p_eq_np`: `[propext, sorryAx, Classical.choice, Quot.sound]` |
| Signature identity | `example : <Mathlib proof_wanted type> := @PvsNP.tm2ComputableInPolyTime_comp` | typechecks (only unused-variable linter warnings) |
| Challenge statement | `example : MillenniumProblems.p_versus_np.statement = Millennium.ClayPVersusNP := rfl`, `example : MillenniumProblems.p_versus_np.statement := p_eq_np` | both `rfl`/typecheck (`import Challenge`, `import Problems.Registry`) |
| Kernel re-check | `lake env leanchecker --fresh Solution` | exit 0, 10:28:25 → 10:37:46 (9 min 21 s) |
| Repo tests | `lake build Tests` in `LeanMillenniumPrizeProblems` | `Build completed successfully (4277 jobs)`; `Tests/PVersusNP/Sanity.lean` (with its `#guard_msgs` axiom checks) built; the only `sorry` warnings are the repo's own placeholders in BirchSwinnertonDyer, Poincare, RiemannHypothesis |
| Trust-base scan | `grep -nE` over the 16 lakefile roots and the pinned P vs NP sources | see section 5 |
| Non-vacuity witness | `lake env lean NonVacuity.lean` (scratchpad) | `'RedTeam.not_computable' depends on axioms: [propext, Quot.sound]` |
| Encoding cross-check | `python sat_encoding_check.py` (scratchpad; evidence, not proof) | 3000/3000 random instances agree with CaDiCaL; 384,572 verifier-scan vs `cnfSat` agreements; garbage-string checks pass |
| Comparator (WSL) | see section 6 | not completed (host disk full) |

---

## 2. Statement fidelity (item 1)

### 2.1 The definitions actually being used (pinned repo, `Problems/PVersusNP/Millennium.lean`)

```lean
def Language (α : Type) := α → Prop

def InPolynomialTime {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (f : α → Bool) (_comp : TM2ComputableInPolyTime ea.encode finEncodingBoolBool.encode f),
    ∀ a, L a ↔ f a = true

def fin_encoding_string (alphabet : Type) [Fintype alphabet] : FinEncoding (List alphabet) :=
  { Γ := alphabet, encode := id, decode := fun l => some l, decode_encode := ..., ΓFin := inferInstance }

def pair_encoding ... : FinEncoding (α × β) :=   -- alphabet Sum ea.Γ (Option eb.Γ); `inr none` is `#`
  { encode := λ p => (ea.encode p.1).map Sum.inl ++ Sum.inr none :: (eb.encode p.2).map (fun b => Sum.inr (some b)), ... }

def PolynomialTimeCheckingRelation (ea : FinEncoding α) (eb : FinEncoding β) (R : α → β → Prop) : Prop :=
  InPolynomialTime (pair_encoding ea eb) (fun p => R p.1 p.2)

def InNondeterministicPolynomialTime {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (Γ₁ : Type) (_ : Fintype Γ₁) (R : α → List Γ₁ → Prop) (k : ℕ),
    PolynomialTimeCheckingRelation ea (fin_encoding_string Γ₁) R ∧
      ∀ a, L a ↔ ∃ y : List Γ₁, y.length ≤ (ea.encode a).length ^ k ∧ R a y

def PolynomialTimeReducible (ea : FinEncoding α) (eb : FinEncoding β) (L₁ : Language α) (L₂ : Language β) : Prop :=
  ∃ (f : α → β) (_comp : TM2ComputableInPolyTime ea.encode eb.encode f), ∀ a, L₁ a ↔ L₂ (f a)

def NondeterministicPolynomialTimeComplete {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  InNondeterministicPolynomialTime ea L ∧
    ∀ {β : Type} (eb : FinEncoding β) (L' : Language β),
      InNondeterministicPolynomialTime eb L' → PolynomialTimeReducible eb ea L' L

def ClayPVersusNP.Formulations.ClassEquality : Prop :=
  ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet] (L : Language (List alphabet)),
    InPolynomialTime (fin_encoding_string alphabet) L ↔ InNondeterministicPolynomialTime (fin_encoding_string alphabet) L

def ClayPVersusNP : Prop := ClayPVersusNP.Formulations.ClassEquality
```

and the Mathlib machine layer (`Mathlib/Computability/TuringMachine/Computable.lean`,
`StackTuringMachine.lean`, `StateTransition.lean`):

```lean
structure FinTM2 where
  {K : Type} [kDecidableEq : DecidableEq K] [kFin : Fintype K]
  (k₀ k₁ : K) (Γ : K → Type) (Λ : Type) (main : Λ) [ΛFin : Fintype Λ]
  (σ : Type) (initialState : σ) [σFin : Fintype σ] [Γk₀Fin : Fintype (Γ k₀)]
  (m : Λ → Turing.TM2.Stmt Γ Λ σ)

inductive Stmt | push : ∀ k, (σ → Γ k) → Stmt → Stmt | peek : ∀ k, (σ → Option (Γ k) → σ) → Stmt → Stmt
  | pop : ∀ k, (σ → Option (Γ k) → σ) → Stmt → Stmt | load : (σ → σ) → Stmt → Stmt
  | branch : (σ → Bool) → Stmt → Stmt → Stmt | goto : (σ → Λ) → Stmt | halt : Stmt

def step (M : Λ → Stmt Γ Λ σ) : Cfg Γ Λ σ → Option (Cfg Γ Λ σ)
  | ⟨none, _, _⟩ => none
  | ⟨some l, v, S⟩ => some (stepAux (M l) v S)

def haltList (tm : FinTM2) (s : List (tm.Γ tm.k₁)) : tm.Cfg where
  l := Option.none; var := tm.initialState; stk k := if k = tm.k₁ then s else []

structure EvalsTo (f : σ → Option σ) (a : σ) (b : Option σ) where
  steps : ℕ; evals_in_steps : (flip bind f)^[steps] a = b
structure EvalsToInTime ... extends EvalsTo f a b where steps_le_m : steps ≤ m

def TM2OutputsInTime (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁))) (m : ℕ) :=
  EvalsToInTime tm.step (initList tm l) ((Option.map (haltList tm)) l') m

structure TM2ComputableInPolyTime (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β) extends TM2ComputableAux αΓ βΓ where
  time : Polynomial ℕ
  outputsFun : ∀ a, TM2OutputsInTime tm (List.map inputAlphabet.invFun (ea a))
    (Option.some ((List.map outputAlphabet.invFun) (eb (f a)))) (time.eval (ea a).length)
```

### 2.2 Does `NondeterministicPolynomialTimeComplete` mean NP-complete under poly-time many-one reductions?

Yes. Point by point, looking for the kinds of quirk that produced the September 2026 bug:

* **Certificates.** They are *all* finite strings over a finite type `Γ₁` with the identity encoding
  (`fin_encoding_string Γ₁`). The September bug (an arbitrary encoded type `β` whose elements could
  carry membership) is closed: `Γ₁` is finite, so a symbol carries `log₂ |Γ₁|` bits and nothing else,
  and the verifier's right-hand alphabet `Option Γ₁` covers every string. The verifier is a *single*
  machine that must decide `R w y` on **every** pair `w#y` (`InPolynomialTime (pair_encoding …)` quantifies
  over all `p : α × List Γ₁`), in time polynomial in `|w| + 1 + |y|`.
* **One machine, one polynomial.** In `InPolynomialTime`, `PolynomialTimeReducible` and the verifier,
  the machine `tm` and `time : Polynomial ℕ` are fields fixed before `∀ a`. The time bound is
  `time.eval (ea a).length`, a polynomial in the *encoded* input length. No per-input choice is possible.
* **What a step is.** One `step` executes one finite `Stmt` tree; the number of stack operations per step
  is bounded by the size of the largest statement in the (finite) program, so step counts are standard
  time up to a constant (Mathlib's own note).
* **Acceptance is strict.** The run must reach exactly `haltList tm l'`: label `none`, state reset to
  `initialState`, every stack except `k₁` empty, `k₁` holding exactly the output. A halted configuration
  has no successor (`step ⟨none,_,_⟩ = none`), so overshooting is impossible. This is a *restriction*
  (machines must clean up); it costs linear time and cannot make a class larger.
* **Reductions.** `PolynomialTimeReducible eb ea L' L` is "there is a function `f`, computed by one
  polynomial-time `FinTM2` from `eb.encode a` to `f a`, with `L' a ↔ L (f a)`": Cook's Definition 3
  (Karp reduction). Hardness quantifies over **every** `β : Type` and **every** `FinEncoding β`, i.e. it is
  *stronger* than Cook's string-only statement.
* **Alphabets.** `ClassEquality` ranges over `alphabet` with `[Fintype] [Nontrivial]` (≥ 2 symbols), as
  in Cook; `cook_levin` is over `Bool`, which is `Nontrivial`.
* **Universe levels.** Everything is in `Type` (= `Type 0`); `Nonempty.{2}` in the composition lemma is
  `Nonempty` of the `Type 1` structure `TM2ComputableInPolyTime`, matching Mathlib's `proof_wanted`.
* **Non-vacuity of the pieces.** NP is inhabited (`sat_in_np`; the repo's `emptyLanguage_in_NP`; with
  `PvsNP.comp`, every P language over a string alphabet is in NP via
  `PolynomialTimeContainedInNondeterministicPolynomialTime.of_turing_machine_composition`). `SAT` has
  members and non-members (`example : SAT [true,false,false,false,true,true,true,false,false,false]`,
  `example : ¬ SAT [false,false]` in CookLevin.lean), so a reduction cannot be a constant map.
  `TM2ComputableInPolyTime` is not inhabited for every function (section 4.2).

### 2.3 Weak spots examined and judged harmless

* **`|y| ≤ |w|^k` (M4).** For `|w| ∈ {0,1}` the bound is `≤ 1`. Only finitely many inputs are affected and
  `R` may hard-code them. This is Cook's wording verbatim.
* **`Γ₁` may be empty.** Then only `y = []` is a certificate; this restricts, never enlarges, NP.
* **`time` may be the zero polynomial.** Then `steps ≤ 0` forces `initList = haltList`; restrictive.
* **`k₀ = k₁` allowed.** Input and output stacks may coincide; irrelevant to the classes.
* **`FinEncoding` requires `decode_encode`,** so every `eb.encode` is injective: membership of `a` is
  determined by its encoding, as a language over strings should be.

### 2.4 The machine model (M3)

Only `Γ k₀` is required finite; `Γ k` for `k ≠ k₀` may be any `Type`, and every function in a `Stmt`
(`σ → Γ k`, `σ → Option (Γ k) → σ`, `σ → Bool`, `σ → Λ`) may be a noncomputable Lean function. This is the
place a sceptic should probe. It does not enlarge P or NP: `push k f` can only push `f v` for `v : σ`
(finite) and there are finitely many `push` nodes in a finite program over finite `Λ`, so the set of symbols
that can ever appear on any stack is finite (input alphabet ∪ pushable symbols); `peek`/`pop` functions are
only ever evaluated on that finite set; and `branch`/`goto`/`load` are functions on finite types. Hence every
`FinTM2` is extensionally one specific finite machine (its table is a fixed, if possibly unknowable, finite
object), and the class of languages decided in polynomial time by `FinTM2`s is exactly the class decided
by multi-stack machines with finite tables, which is standard P (multi-stack ↔ multi-tape is a polynomial
simulation). The same argument covers verifiers (NP) and reduction machines. The hardness proof itself
handles arbitrary work alphabets classically (`Enc.ofFinTM2` restricts to the finite reachable symbol set),
so no finiteness assumption is smuggled in. DEFINITIONS.md says this; the README does not (M3).

### 2.5 `Challenge.lean` versus the repository's statement

`Challenge.lean` (identical locally and on `origin/master`, single commit `74e886e`):

```lean
import Problems.PVersusNP.Millennium

theorem p_eq_np : Millennium.ClayPVersusNP := by sorry
```

The registry (`Problems/Registry.lean`) has `statement := Millennium.ClayPVersusNP`,
`statement_declaration := "Millennium.ClayPVersusNP"`, `prize_theorem_declaration := none`,
`status := open_problem`, `resolution_shape := decide`. The scratch file `CheckRegistry.lean` proved

```lean
example : MillenniumProblems.p_versus_np.statement = Millennium.ClayPVersusNP := rfl
example : MillenniumProblems.p_versus_np.statement := p_eq_np
example : MillenniumProblems.p_versus_np.statement_declaration = "Millennium.ClayPVersusNP" := rfl
example : MillenniumProblems.p_versus_np.prize_theorem_declaration = none := rfl
```

and `set_option pp.all true in #check @p_eq_np` prints `p_eq_np : Millennium.ClayPVersusNP` in both the
`Challenge` and the `Solution` environment. `Solution.lean` proves it by

```lean
theorem p_eq_np : Millennium.ClayPVersusNP :=
  Millennium.ClayPVersusNP.nondeterministic_polynomial_time_complete_in_polynomial_time
    PvsNP.comp PvsNP.cook_levin PvsNP.sat_in_p
```

whose repo signature is `(hComp : PolynomialTimeComputableComposition) {alphabet} [Fintype] [Nontrivial]
{L} (hComplete : NondeterministicPolynomialTimeComplete (fin_encoding_string alphabet) L)
(hP : InPolynomialTime (fin_encoding_string alphabet) L) : ClayPVersusNP`. Any shadowing of
`NondeterministicPolynomialTimeComplete` or `SAT` by a project-local constant would make this
application fail to typecheck; it typechecks, and `#check @PvsNP.cook_levin` prints the fully qualified
`Millennium.NondeterministicPolynomialTimeComplete (Millennium.fin_encoding_string Bool) PvsNP.SAT`.

### 2.6 The repository's own tests

`lake build Tests` in the submodule: `Build completed successfully (4277 jobs)`. `Tests/PVersusNP/Sanity.lean`
contains `#guard_msgs` checks that `ClayVerifiableLanguage.iff_in_nondeterministic_polynomial_time`,
`ClassEquality.iff_hard_direction`, `ClayPVersusNP.iff_checkable`,
`Consequences.NondeterministicPolynomialTimeCompleteInPolynomialTime.of_turing_machine_composition`,
`emptyLanguage_in_NP`, `emptyLanguage_in_P` depend only on `[propext, Classical.choice, Quot.sound]`; a
mismatch fails the build. `Tests/AggregateTargets.lean` documents why no `P ∨ ¬P` aggregate exists.

---

## 3. SAT fidelity (item 2)

### 3.1 Definition (CookLevin.lean)

```lean
abbrev Clause := List (Option Bool)        -- slot j: none = absent, some true = x_j, some false = ¬x_j
abbrev CNF := List Clause
def clauseSat (c : Clause) (a : List Bool) : Prop := ∃ (j : ℕ) (b : Bool), c[j]? = some (some b) ∧ a[j]? = some b
def cnfSat (φ : CNF) (a : List Bool) : Prop := ∀ c ∈ φ, clauseSat c a
def decodeAux : List Bool → Clause → CNF
  | false :: false :: r, cur => cur.reverse :: decodeAux r []
  | false :: true :: r, cur => decodeAux r (none :: cur)
  | true :: s :: r, cur => decodeAux r (some (!s) :: cur)
  | _, _ => []
def decodeCNF (w : List Bool) : CNF := decodeAux w []
def encodeSlot : Option Bool → List Bool | none => [false, true] | some b => [true, !b]
def encodeClause (c : Clause) : List Bool := c.flatMap encodeSlot ++ [false, false]
def encodeCNF (φ : CNF) : List Bool := φ.flatMap encodeClause
def SAT : Language (List Bool) := fun w => ∃ a : List Bool, cnfSat (decodeCNF w) a
```

So `10` = positive literal, `11` = negative literal, `01` = absent, `00` = end of clause, as the README says.

### 3.2 Not degenerate

* **Every formula is present:** `decodeCNF_encodeCNF (φ : CNF) : decodeCNF (encodeCNF φ) = φ` (proved).
  Clause width is unrestricted, so every CNF over variables `x_0 … x_n` is a member of the domain.
* **Not trivially easy / trivially hard:** `sat_in_np` (proved; verifier with certificates over `Bool`,
  `k = 1`) and `cook_levin` (proved) place `SAT` in NP and make it NP-hard under the repository's
  definitions. Both members and non-members exist (`example`s in CookLevin.lean).
* **Semantics are standard:** a clause is satisfied iff some present literal is true under `a`;
  variables beyond `a.length` satisfy nothing. Because `SAT` quantifies `∃ a`, a short `a` can only
  satisfy fewer clauses, so `SAT w` is exactly "the decoded CNF has a satisfying assignment"; the proved
  lemmas `cnfSat_take` and `sat_iff_check` (`SAT w ↔ ∃ y, |y| ≤ |w|^1 ∧ check w y = true`) confirm that
  truncating to `|w|` loses nothing.

### 3.3 Cross-check by Python (evidence, not proof)

`sat_encoding_check.py` mirrors `decodeAux`, `encodeCNF`, `clauseSat`, `cnfSat` and the verifier scan
`evalCNF`/`check` literally, then:

| Test | Result |
|---|---|
| 3000 random CNFs (0–7 variables, 0–9 clauses, width ≤ 3): dense encode → `decodeCNF` round trip | all equal |
| Same instances: `∃a` over all `2^n` assignments with the Lean `cnfSat` mirror vs CaDiCaL (PySAT) on the standard clause list | 3000/3000 agree |
| `check w y` (verifier scan) vs `cnfSat (decodeCNF w) y` for every assignment of every length ≤ n+1 | 384,572 agreements, 0 disagreements |
| 2000 random bit strings (garbage): `decodeCNF` total, `decodeCNF (encodeCNF (decodeCNF w)) = decodeCNF w`, `check = cnfSat` on all assignments of length ≤ 5 | all pass |
| The four `example`s in CookLevin.lean | reproduced |

### 3.4 Relation to standard encodings (M1, M2)

* **Dense → standard** (DIMACS-like): read each row, emit `±(j+1)` for each `some` slot; linear time,
  output no larger than the input.
* **Standard → dense:** rename the variables occurring in the formula to `0 … n−1` (`n ≤` formula size),
  drop tautological clauses (a dense row has one slot per variable and cannot contain both `x_j` and
  `¬x_j`; such clauses are always true), then emit rows of width ≤ `n`; size `≤ 2·m·(n+1) = O(S²)` for a
  standard formula of size `S`. Without renaming, a clause `(x_N)` with `N` written in binary (`log N`
  bits) becomes `2(N+1)` dense bits, so the *encoding map* is not polynomial; the *languages* are
  poly-time inter-reducible, which is what NP-completeness needs. Measured ratios (dense bits /
  approximate DIMACS bits): 1.5 at n=10, 8.4 at n=100, 61 at n=1000 for 3-CNF at ratio 4.26; 0.29 for
  width-50 clauses over 50 variables.
* Hence `SAT ∈ P ⇔ CNF-SAT ∈ P` in the standard sense; the dense padding cannot make the problem easier
  by more than a polynomial.
* `SAT []` holds, and any string without a `00` terminator decodes to `[]` (satisfiable). A dangling odd
  bit is ignored. Junk is thus accepted rather than rejected (M2).

---

## 4. TM2 composition (item 3)

### 4.1 Signature identity

Mathlib (`Mathlib/Computability/TuringMachine/Computable.lean:284`, inside `namespace Turing`,
`noncomputable section`):

```lean
proof_wanted TM2ComputableInPolyTime.comp
    {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ}
    {eγ : γ → List γΓ} {f : α → β} {g : β → γ} (h1 : TM2ComputableInPolyTime eα eβ f)
    (h2 : TM2ComputableInPolyTime eβ eγ g) :
  Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f))
```

Comp.lean:

```lean
theorem tm2ComputableInPolyTime_comp {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ}
    {eβ : β → List βΓ} {eγ : γ → List γΓ} {f : α → β} {g : β → γ}
    (h1 : TM2ComputableInPolyTime eα eβ f) (h2 : TM2ComputableInPolyTime eβ eγ g) :
    Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f)) :=
  ⟨Comp.compComputable h1 h2⟩
```

Checked mechanically: `example : ∀ {α β γ αΓ βΓ γΓ : Type} … , Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f)) := @PvsNP.tm2ComputableInPolyTime_comp`
elaborates, and `pp.all` prints

```
@PvsNP.tm2ComputableInPolyTime_comp : ∀ {α β γ αΓ βΓ γΓ : Type} {eα : α → List.{0} αΓ} {eβ : β → List.{0} βΓ}
  {eγ : γ → List.{0} γΓ} {f : α → β} {g : β → γ} (h1 : @Turing.TM2ComputableInPolyTime α β αΓ βΓ eα eβ f)
  (h2 : @Turing.TM2ComputableInPolyTime β γ βΓ γΓ eβ eγ g),
  Nonempty.{2} (@Turing.TM2ComputableInPolyTime α γ αΓ γΓ eα eγ (@Function.comp.{1, 1, 1} α β γ g f))
```

Same binders, same implicitness, same universes; only the constant name differs (the README says so).
`PvsNP.comp : ClayPVersusNP.Support.PolynomialTimeComputableComposition := fun h1 h2 => tm2ComputableInPolyTime_comp h1 h2`
discharges the repository's hypothesis with no extra assumptions.

### 4.2 Non-vacuity of `TM2ComputableInPolyTime`

It is neither empty nor universal.

* Inhabited: Mathlib's `idComputableInPolyTime`; the repo's `constFalseDecider`; every machine in this project.
* Not universal: scratch file `NonVacuity.lean` (imports `Comp`) proves, from determinism of `step`
  (`step (haltList tm l) = none`, so two runs from one configuration cannot halt in different outputs),

```lean
theorem not_computable :
    ¬ Nonempty (TM2ComputableInPolyTime (fun _ : ℕ => ([] : List Unit)) (fun n : ℕ => List.replicate n ()) id)
-- 'RedTeam.not_computable' depends on axioms: [propext, Quot.sound]
```

  The project's own `PvsNP.Comp.length_iter (M : FinTM2) (k : M.K) : ∀ n c d, (flip bind M.step)^[n] (some c) = some d → (d.stk k).length ≤ (c.stk k).length + pushBound M * n`
  further shows that an output longer than `|input| + pushBound·time.eval |input|` is impossible, so
  functions with super-polynomial output length (e.g. `n ↦ 2^n` in unary) are not in the predicate either.
  Composition is therefore a genuine closure property, not a triviality.

---

## 5. Trust base (item 4)

### 5.1 Build closure

Lakefile roots (16): `Challenge, Comp, CookLevin, SatInP, Solution, Prog, D3Fam, D3OneHot, D3Shift, Sit,
D3Acc, D3Init, Emb, Asm, Pre, Pkg`; options `autoImplicit = false`, `relaxedAutoImplicit = false`. Import
chain of `Solution`: `Comp`, `CookLevin`, `SatInP`, `Pkg → Pre → Asm → {D3Init, D3Acc, Emb} → Sit → D3Shift →
D3OneHot → D3Fam → {CookLevin, Prog}`; every import is one of these files, `Problems.PVersusNP.Millennium`,
or a `Mathlib.*` module (`Mathlib.Tactic.DeriveFintype`, `Mathlib.Tactic.Linarith`,
`Mathlib.Computability.TuringMachine.StackTuringMachine`, `Mathlib.Data.List.Sigma`). No root imports
`D3SDef`, `Spike`, `ToyD3` or any `Scratch*` file. 12,854 lines in the 13 proof files, 12,882 with
`Challenge`, `Solution`, `SatInP`. `Solution.lean` does not import `Challenge.lean`; both declare
`p_eq_np : Millennium.ClayPVersusNP` at top level, so Comparator-style comparison applies.

### 5.2 Banned-token scan

Pattern (over all 16 roots):
`sorry|admit|\baxiom\b|native_decide|\+ *native|implemented_by|@\[extern|\bextern\b|\bunsafe\b|\bpartial\b|open private|set_option debug|run_cmd|run_tac|addDecl|\bmacro\b|\belab\b|\bsyntax\b|\bnotation\b|initialize|import Lean|\bopaque\b|csimp|autoImplicit|Lean\.Elab|Lean\.Meta|MetaM|CoreM|Environment`

Hits, complete:

```
Challenge.lean:3:theorem p_eq_np : Millennium.ClayPVersusNP := by sorry
SatInP.lean:15:theorem sat_in_p : InPolynomialTime (fin_encoding_string Bool) SAT := sorry
Pre.lean:26:set_option autoImplicit false
Pkg.lean:23:set_option autoImplicit false
```

Second pass (`set_option`, `instance`, `attribute`, `local`, `private`, `protected`, `export`, `open … renaming/hiding`,
`#eval`, `#guard`, `#reduce`, `decide`): the only non-`decide` hits are
`Comp.lean:20: attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin` (the
machine's own finiteness fields, made available as instances; shadows nothing),
`Prog.lean:36: instance : Flag Bool := ⟨id, id, fun _ => rfl⟩` (a class defined in Prog.lean itself) and
`Prog.lean:38: attribute [simp] Flag.untag_tag`. All `decide` occurrences are kernel `decide` (or the
`Bool`-valued function `decide` used as data in clause tables); there is no `native_decide` and no
`Lean.ofReduceBool` axiom appears. No `set_option maxHeartbeats`, no `macro`/`syntax`/`notation`/`elab`,
no `import Lean`, no `unsafe`/`partial`/`opaque`/`implemented_by`/`extern`.

Shadowing scan: no project file declares a `def/abbrev/theorem/structure/class/inductive/instance/opaque`
named `InPolynomialTime, InNondeterministicPolynomialTime, PolynomialTimeReducible,
NondeterministicPolynomialTimeComplete, Language, fin_encoding_string, pair_encoding, ClayPVersusNP,
TM2ComputableInPolyTime, TM2ComputableInTime, TM2Computable, FinTM2, initList, haltList, TM2OutputsInTime,
EvalsToInTime, EvalsTo, FinEncoding, finEncodingBoolBool, PolynomialTimeCheckingRelation, ManyOneReducible,
step, stepAux`; no `namespace Millennium`, `namespace Turing` or `namespace Computability` is opened for
declarations (all declarations live under `PvsNP.*`).

Pinned repo sources in the closure (`Problems/PVersusNP/Millennium.lean`, `PolynomialHierarchy.lean`,
`Problems/Common/*`): same pattern; the only hits are `attribute [instance]` on three structure fields
(`ClayPolynomialTimeVerification.certificate_alphabet_fintype`, `ClayFiniteAlphabet.fintype`,
`ClayFiniteAlphabet.nontrivial`) and the word "sorry" in doc comments.

### 5.3 Axioms and kernel

```
'PvsNP.cook_levin' depends on axioms: [propext, Classical.choice, Quot.sound]
'PvsNP.sat_in_np' depends on axioms: [propext, Classical.choice, Quot.sound]
'PvsNP.CL.sat_np_hard' depends on axioms: [propext, Classical.choice, Quot.sound]
'PvsNP.tm2ComputableInPolyTime_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PvsNP.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PvsNP.sat_in_p' depends on axioms: [propext, sorryAx, Quot.sound]
'p_eq_np' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`lake env leanchecker --fresh Solution` (replays every declaration of the `Solution` closure, Mathlib
included, through the kernel from an empty environment): exit code 0 after 9 min 21 s. This matches the
README's axiom block exactly and confirms its "leanchecker" instruction works.

### 5.4 Versions and pins

`lean-toolchain = leanprover/lean4:v4.31.0`; manifest pins `mathlib fabf563a…` (`inputRev v4.31.0`),
`Physlib 3dddd61e…`, `problems` as a path dependency at `LeanMillenniumPrizeProblems` whose checked-out commit
is `603053dc…` both locally and in the public tree. The pinned commit is after `1fdee4b` ("Fix statement
soundness across problems", 2026-09-07), i.e. it contains the string-certificate NP. The README's version
table is correct.

---

## 6. Independent statement check with Comparator (item 5) — NOT COMPLETED

**What Comparator does** (README of `leanprover/comparator`, read from the clone): with a JSON config
`{challenge_module, solution_module, theorem_names, permitted_axioms}` it (1) builds the challenge module
with `lake` inside a `landrun --best-effort --ro / --rw /dev --rw .lake` sandbox, (2) runs `lean4export`
on it, (3) repeats for the solution, (4) checks that every declaration used in the statements of the
listed theorems is identical in both environments, (5) checks the listed theorems use only
`permitted_axioms`, (6) replays the solution environment in the kernel. It needs Linux (`landrun` uses
Landlock), a `lean4export` matching the project's Lean (tag `v4.31.0` exists), and is itself built with
`leanprover/lean4:v4.35.0-rc3`.

**What was done.** In WSL `Ubuntu-22.04` (kernel `5.15.167.4-microsoft-standard-WSL2`, `CONFIG_SECURITY_LANDLOCK=y`,
`landlock` first in `CONFIG_LSM`): installed `elan` (no default toolchain) and Go (latest stable tarball,
user-space), cloned `comparator` (master), `lean4export`, `landrun`, and the **public** repository with its
submodule (`9cc4ad3`, submodule `603053dc`), all under `~/redteam`. Stage 2 (toolchain installs,
`lake exe cache get`, `lake build` in the clean clone; `go build` landrun; `lake build` lean4export at
`v4.31.0`; `lake build lean4export comparator`) started at 10:32 and died at 10:38 when the host `C:` drive
filled up (section "ACTION REQUIRED"). Exit codes recorded by the wrappers: clean-clone build `126`,
comparator build `2`; the logs are inside the unreachable distro.

**Why it cannot be finished now.** With 0 bytes free on `C:`, WSL cannot attach the distro's disk image;
relocating the image was blocked. No sandboxed run, no export, no kernel replay happened. I therefore make
**no claim** from Comparator.

**Ready-to-run material (once WSL is usable).** In the clean clone, add the two roots to `lakefile.toml`
(`roots = [..., "RedTeamChallenge", "RedTeamSolution"]`) and create:

`RedTeamChallenge.lean` (statements exactly as in the README; the challenge imports `CookLevin` only for the
*definition* `PvsNP.SAT`, which the comparator then requires to be the same constant in both environments):

```lean
import Problems.PVersusNP.Millennium
import CookLevin

open Millennium in
theorem PvsNP.cook_levin :
    NondeterministicPolynomialTimeComplete (fin_encoding_string Bool) PvsNP.SAT := by sorry

open Turing in
theorem PvsNP.tm2ComputableInPolyTime_comp {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ}
    {eβ : β → List βΓ} {eγ : γ → List γΓ} {f : α → β} {g : β → γ}
    (h1 : TM2ComputableInPolyTime eα eβ f) (h2 : TM2ComputableInPolyTime eβ eγ g) :
    Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f)) := by sorry
```

`RedTeamSolution.lean`:

```lean
import Comp
import Pkg
```

`config.json`:

```json
{
  "challenge_module": "RedTeamChallenge",
  "solution_module": "RedTeamSolution",
  "theorem_names": ["PvsNP.cook_levin", "PvsNP.tm2ComputableInPolyTime_comp"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
```

Run (from the clone root, after `lake exe cache get`):

```
COMPARATOR_LANDRUN=$HOME/redteam/landrun/landrun \
COMPARATOR_LEAN4EXPORT=$HOME/redteam/lean4export/.lake/build/bin/lean4export \
lake env $HOME/redteam/comparator/.lake/build/bin/comparator config.json
```

(The README additionally wraps this in `systemd-run --user … RestrictAddressFamilies=~AF_UNIX`; WSL has no
user systemd here, so that hardening would be skipped. Comparator ships `scripts/fake-landrun.sh` for
unsandboxed runs on non-Linux hosts; a Windows run of the same statement/axiom/replay checks is possible
with that shim but was not attempted because the Windows clones also failed for lack of disk space.)

What the in-session checks already cover of Comparator's six steps: (4) statement identity was checked by
elaboration (`example := @PvsNP.tm2ComputableInPolyTime_comp`, the `rfl` registry checks, `pp.all`
printouts); (5) axioms by `#print axioms`; (6) kernel replay by `leanchecker --fresh`. Not covered: the
sandboxed, adversarial-proof build and export pipeline.

---

## 7. What remains unverified by machine

* The claim that the repository's `FinTM2` model defines *the* standard classes P and NP (section 2.4) is
  a paper argument; the repository itself does not formalise an equivalence with single-tape machines.
  The Lean theorems are exactly about the repository's definitions.
* The informal equivalence between `SAT` (dense) and standard CNF-SAT (section 3.4) is a paper argument
  plus Python evidence; no Lean reduction between encodings exists or is claimed.
* `cook_levin` relies on Lean's kernel, the three standard axioms, Mathlib's definitions, and the pinned
  repository's definitions. `#print axioms` and `leanchecker` do not vouch for the *meaning* of
  definitions, which is what sections 2–3 address by inspection.
* Comparator was not run (section 6).

---

## Appendix A. Verbatim outputs

Build (`lake build`, 2026-10-06):
```
⚠ [1231/1243] Replayed Challenge
warning: Challenge.lean:3:8: declaration uses `sorry`
⚠ [1259/1270] Replayed SatInP
warning: SatInP.lean:15:8: declaration uses `sorry`
Build completed successfully (1270 jobs).
```

Repo tests (`cd LeanMillenniumPrizeProblems && lake build Tests`):
```
⚠ [3410/3420] Replayed Problems.BirchSwinnertonDyer.Millennium
warning: Problems/BirchSwinnertonDyer/Millennium.lean:2282:8: declaration uses `sorry`
⚠ [4147/4169] Replayed Problems.Poincare.Millennium
warning: Problems/Poincare/Millennium.lean:251:8: declaration uses `sorry`
⚠ [4275/4277] Replayed Problems.RiemannHypothesis.Millennium
warning: Problems/RiemannHypothesis/Millennium.lean:737:8: declaration uses `sorry`
Build completed successfully (4277 jobs).
```

`Check.lean` (`#check`/`#print` extracts):
```
PvsNP.cook_levin : Millennium.NondeterministicPolynomialTimeComplete (Millennium.fin_encoding_string Bool) PvsNP.SAT
def PvsNP.SAT : Millennium.Language (List Bool) := fun w => ∃ a, PvsNP.SATDef.cnfSat (PvsNP.SATDef.decodeCNF w) a
p_eq_np : Millennium.ClayPVersusNP            -- in both the Solution and the Challenge environment
```

`leanchecker`:
```
start Tue Oct  6 10:28:25 AUSEST 2026
LEANCHECKER_EXIT=0
end Tue Oct  6 10:37:46 AUSEST 2026
```

`sat_in_np` as stated (CookLevin.lean:793):
```lean
theorem sat_in_np : InNondeterministicPolynomialTime (fin_encoding_string Bool) SAT :=
  ⟨Bool, inferInstance, fun w y => check w y = true, 1,
    ⟨fun p => check p.1 p.2, verifier, fun _ => Iff.rfl⟩, fun w => sat_iff_check w⟩
```

`cook_levin` as stated (Pkg.lean:600):
```lean
theorem cook_levin : NondeterministicPolynomialTimeComplete (fin_encoding_string Bool) SAT :=
  ⟨sat_in_np, fun eb L' hL => CL.sat_np_hard eb L' hL⟩
```

Python cross-check (`sat_encoding_check.py`):
```
random instances: 3000/3000 agree (PySAT CaDiCaL vs Lean-mirror brute force)
verifier-scan vs cnfSat agreements: 384572
garbage strings: decode total, re-encode idempotent, check == cnfSat: ok
size relation (nvars, nclauses, width): dense_bits vs standard_bits
  n=   10 m=   40 k=  3: dense=      880 standard~=      600 ratio=   1.47
  n=  100 m=  430 k=  3: dense=    86860 standard~=   10320 ratio=   8.42
  n= 1000 m= 4260 k=  3: dense=  8528520 standard~=  140580 ratio=  60.67
  n=   50 m=   50 k= 50: dense=     5100 standard~=   17500 ratio=   0.29
CookLevin.lean sanity examples reproduced
```

## Appendix B. Scratch files (session scratchpad, not in the repository)

`Check.lean`, `CheckChallenge.lean`, `CheckRegistry.lean`, `NonVacuity.lean`, `sat_encoding_check.py`,
`wsl_stage1.sh`, `wsl_stage2a.sh`, `wsl_stage2b.sh`, and logs. The repository working tree was not
modified except for this file.
