# Cook-Levin against the Clay P vs NP statement, in Lean 4

**This repository does not prove P = NP or P ≠ NP.** The final theorem `p_eq_np` still depends on one `sorry`, `sat_in_p` (SAT ∈ P), which is the open problem itself.

What it does prove, with no `sorry` and only Lean's three standard axioms, against the definitions in [LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems) (commit `603053d`):

1. **Cook-Levin** (`PvsNP.cook_levin`, in `Pkg.lean`): SAT is NP-complete.

```lean
   theorem cook_levin : NondeterministicPolynomialTimeComplete (fin_encoding_string Bool) SAT
   ```

   This uses the repository's verifier-based definition of NP, Mathlib's multi-stack `FinTM2` machines, and polynomial-time many-one reductions from NP languages under every finite encoding.

   Two caveats on these definitions. Mathlib's `FinTM2` requires only the input-stack alphabet to be finite and allows transition tables to be arbitrary (noncomputable) Lean functions; `DEFINITIONS.md` explains why only finitely many symbols are ever reachable, so this does not enlarge P or NP. The repository's NP bounds certificates by `|y| ≤ |w|^k`, as in Cook's wording, so inputs of length 0 or 1 admit certificates of length at most 1; this affects finitely many inputs only.

2. **Composition of polynomial-time TM2 machines** (`PvsNP.tm2ComputableInPolyTime_comp`, in `Comp.lean`), with the same signature as Mathlib's `proof_wanted TM2ComputableInPolyTime.comp`. This discharges the `PolynomialTimeComputableComposition` assumption used by the repository's reduction lemmas, so P ⊆ NP and closure of P under reductions become unconditional.

## Status

|Result|Status|
|-|-|
|SAT ∈ NP (`PvsNP.sat_in_np`)|proved|
|SAT is NP-hard (`PvsNP.CL.sat_np_hard`)|proved|
|Cook-Levin (`PvsNP.cook_levin`)|proved|
|TM2 composition (`PvsNP.tm2ComputableInPolyTime_comp`)|proved|
|SAT ∈ P (`PvsNP.sat_in_p`)|**open** (`sorry`): this is the P vs NP problem|
|`p_eq_np`|not proved (depends on `sat_in_p`)|

Axiom check output:

```
'PvsNP.cook_levin' depends on axioms: \[propext, Classical.choice, Quot.sound]
'p_eq_np' depends on axioms: \[propext, sorryAx, Classical.choice, Quot.sound]
```

The `sorryAx` in `p_eq_np` comes only from `sat_in_p`.

## The SAT encoding

`cook_levin` is a statement about one specific language, `PvsNP.SAT : Language (List Bool)`, defined in `CookLevin.lean`:

* A CNF formula is a list of clauses. Each clause is a row with one slot per variable: absent, positive literal, or negative literal.
* Each slot takes 2 bits: `00` ends a clause, `01` absent, `10` positive, `11` negative. Decoding is total; an unfinished final clause is ignored.
* An assignment is a `List Bool`. Variables beyond its length are unassigned and satisfy no literal.
* `SAT w` holds when some assignment satisfies `decodeCNF w`. Clause width is unrestricted, so this is general SAT, not k-SAT.
* Junk strings are members: `SAT []` holds, and any string with no `00` terminator decodes to the empty formula, which is satisfiable. Such strings form a linear-time recognisable set, so this does not affect complexity.
* The dense encoding is polynomially related to standard CNF encodings (such as DIMACS) only after renumbering variables. Without renumbering, a clause mentioning variable `x_N`, whose index takes about `log N` bits in a standard encoding, costs `2(N+1)` dense bits. Converting a standard formula renames its variables to `0 … n−1` and drops tautological clauses (a dense row cannot hold both `x_j` and `¬x_j`); the two languages are then polynomial-time inter-reducible, which is what NP-completeness needs. This equivalence is a paper argument; no Lean reduction between encodings is claimed.

## Verifying

Requirements: [elan](https://github.com/leanprover/elan) and Git.

```
git clone --recurse-submodules <this repository's URL>
cd <repository folder>
lake exe cache get
lake build
```



If you cloned without `--recurse-submodules`, run `git submodule update --init` first.



The build should finish with exactly two `sorry` warnings:

```
warning: Challenge.lean:3:8: declaration uses `sorry`
warning: SatInP.lean:15:8: declaration uses `sorry`
```

`Challenge.lean` holds the untouched target statement and is meant to keep its `sorry`. `SatInP.lean` is the open problem.

To check axioms, create a file `Check.lean` containing

```lean
import Solution
#print axioms PvsNP.cook_levin
#print axioms p_eq_np
```

and run `lake env lean Check.lean`.

To re-check every declaration with the Lean kernel, starting from an empty environment (`leanchecker` ships with Lean v4.28.0 and later):

```
lake env leanchecker --fresh Solution
```

## File map

|File|Contents|
|-|-|
|`Comp.lean`|Composition of polynomial-time TM2 machines|
|`CookLevin.lean`|SAT definition and encoding; SAT ∈ NP via an explicit verifier machine|
|`Prog.lean`|Loop and counter library for hand-written TM2 machines|
|`D3Fam.lean`, `D3Shift.lean`, `D3Acc.lean`, `D3Init.lean`|Machines that generate each clause family, with polynomial time bounds|
|`D3OneHot.lean`|Generator library (its one-hot clause family is not used in the final formula)|
|`Sit.lean`|Situation tables for an arbitrary `FinTM2`, the step-agreement theorem, and soundness and completeness of the formula (`five_iff`)|
|`Emb.lean`|Running a machine inside a larger machine (stack embedding)|
|`Asm.lean`|Sequencing the generators into one machine|
|`Pre.lean`|Precomputation from the raw input|
|`Pkg.lean`|Halting cleanup, packaging as `TM2ComputableInPolyTime`, and `cook_levin`|
|`Challenge.lean`|The target statement `Millennium.ClayPVersusNP`, left as `sorry`|
|`SatInP.lean`|`sat_in_p`, open|
|`Solution.lean`|Derives `p_eq_np` from `cook_levin` and `sat_in_p`|
|`scratch/`|Exploratory or scratch files (`D3SDef.lean`, `Spike.lean`, `ToyD3.lean`, `Scratch*.lean`), not part of the proof or the build|
|`logs/`|Build logs from development sessions|
|`NOTES.md`|Development log, design decisions, lemma table|
|`DEFINITIONS.md`|Summary of the LeanMillenniumPrizeProblems definitions used|

## Further work in this repository

* [`PHASE3.md`](PHASE3.md): a barrier survey and paper screen of candidate approaches to SAT ∈ P, with a pre-registered falsification plan for the candidate it recommended testing (C3, SDCL with PR learning).
* [`PHASE4.md`](PHASE4.md): the experiment that ran that plan. The candidate was falsified: it hit the time cap on several benchmark families under the pre-registered kill criteria (it gave no wrong answers).
* [`REDTEAM.md`](REDTEAM.md): an adversarial review of the proved results. It found no critical or major issues; its four minor documentation findings are reflected in the caveats above.

In short, one candidate approach to SAT ∈ P was screened on paper and then falsified experimentally. `sat_in_p` remains open.

## Prior work

Cook-Levin has been formalized several times, including by Gäher and Kunze (Coq, ITP 2021), Balbach (Isabelle AFP, 2023), and in Lean 4 by [Complexitylib](https://github.com/SamuelSchlesinger/complexitylib) and others. Those developments use their own machine models and definitions.

What distinguishes this one is that it is stated against the LeanMillenniumPrizeProblems definitions, so it plugs directly into that repository's formal P vs NP statement without a separate proof that the machine models agree.

For TM2 composition, an independent Mathlib pull request ([#44441](https://github.com/leanprover-community/mathlib4/pull/44441)) was open at the time of writing.

## How this was made

The Lean code was written by an AI coding agent (Claude Code, by Anthropic) over a series of scoped sessions that I directed. For each session I set the goal and the rules (no `sorry`, `axiom`, `native_decide`, or environment-modifying metaprogramming in proved code; statements written down before proving them), reviewed the session's report, and independently ran the build, axiom, and `leanchecker` checks described above. `NOTES.md` records the development session by session.

## Versions

* Lean v4.31.0
* Mathlib v4.31.0 (`fabf563a`)
* LeanMillenniumPrizeProblems `603053d` (Git submodule)
* Physlib `3dddd61e`

## License

Copyright 2026 Joshua Tan. Licensed under the Apache License, Version 2.0; see `LICENSE`. LeanMillenniumPrizeProblems, Mathlib and Physlib are separate projects under their own licenses. `phase4/instances` contains third-party benchmark files (SATLIB, SAT Competition 2023), which remain under their own terms. `phase4/tools/dpr-trim` is a Git submodule under its own licence.

