# Cook-Levin against the Clay P vs NP statement, in Lean 4

**This repository does not prove P = NP or P ≠ NP.** The final theorem `p\_eq\_np` still depends on one `sorry`, `sat\_in\_p` (SAT ∈ P), which is the open problem itself.

What it does prove, with no `sorry` and only Lean's three standard axioms, against the definitions in [LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems) (commit `603053d`):

1. **Cook-Levin** (`PvsNP.cook\_levin`, in `Pkg.lean`): SAT is NP-complete.

```lean
   theorem cook\_levin : NondeterministicPolynomialTimeComplete (fin\_encoding\_string Bool) SAT
   ```

   This uses the repository's verifier-based definition of NP, Mathlib's multi-stack `FinTM2` machines, and polynomial-time many-one reductions from NP languages under every finite encoding.

2. **Composition of polynomial-time TM2 machines** (`PvsNP.tm2ComputableInPolyTime\_comp`, in `Comp.lean`), with the same signature as Mathlib's `proof\_wanted TM2ComputableInPolyTime.comp`. This discharges the `PolynomialTimeComputableComposition` assumption used by the repository's reduction lemmas, so P ⊆ NP and closure of P under reductions become unconditional.

## Status

|Result|Status|
|-|-|
|SAT ∈ NP (`PvsNP.sat\_in\_np`)|proved|
|SAT is NP-hard (`PvsNP.CL.sat\_np\_hard`)|proved|
|Cook-Levin (`PvsNP.cook\_levin`)|proved|
|TM2 composition (`PvsNP.tm2ComputableInPolyTime\_comp`)|proved|
|SAT ∈ P (`PvsNP.sat\_in\_p`)|**open** (`sorry`): this is the P vs NP problem|
|`p\_eq\_np`|not proved (depends on `sat\_in\_p`)|

Axiom check output:

```
'PvsNP.cook\_levin' depends on axioms: \[propext, Classical.choice, Quot.sound]
'p\_eq\_np' depends on axioms: \[propext, sorryAx, Classical.choice, Quot.sound]
```

The `sorryAx` in `p\_eq\_np` comes only from `sat\_in\_p`.

## The SAT encoding

`cook\_levin` is a statement about one specific language, `PvsNP.SAT : Language (List Bool)`, defined in `CookLevin.lean`:

* A CNF formula is a list of clauses. Each clause is a row with one slot per variable: absent, positive literal, or negative literal.
* Each slot takes 2 bits: `00` ends a clause, `01` absent, `10` positive, `11` negative. Decoding is total; an unfinished final clause is ignored.
* An assignment is a `List Bool`. Variables beyond its length are unassigned and satisfy no literal.
* `SAT w` holds when some assignment satisfies `decodeCNF w`. Clause width is unrestricted, so this is general SAT, not k-SAT.

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
#print axioms PvsNP.cook\_levin
#print axioms p\_eq\_np
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
|`Sit.lean`|Situation tables for an arbitrary `FinTM2`, the step-agreement theorem, and soundness and completeness of the formula (`five\_iff`)|
|`Emb.lean`|Running a machine inside a larger machine (stack embedding)|
|`Asm.lean`|Sequencing the generators into one machine|
|`Pre.lean`|Precomputation from the raw input|
|`Pkg.lean`|Halting cleanup, packaging as `TM2ComputableInPolyTime`, and `cook\_levin`|
|`Challenge.lean`|The target statement `Millennium.ClayPVersusNP`, left as `sorry`|
|`SatInP.lean`|`sat\_in\_p`, open|
|`Solution.lean`|Derives `p\_eq\_np` from `cook\_levin` and `sat\_in\_p`|
|`D3SDef.lean`, `Spike.lean`, `ToyD3.lean`, `Scratch\*.lean`|Exploratory or scratch files, not part of the proof|
|`NOTES.md`|Development log, design decisions, lemma table|
|`DEFINITIONS.md`|Summary of the LeanMillenniumPrizeProblems definitions used|

## Prior work

Cook-Levin has been formalized several times, including by Gäher and Kunze (Coq, ITP 2021), Balbach (Isabelle AFP, 2023), and in Lean 4 by [Complexitylib](https://github.com/SamuelSchlesinger/complexitylib) and others. Those developments use their own machine models and definitions.

What distinguishes this one is that it is stated against the LeanMillenniumPrizeProblems definitions, so it plugs directly into that repository's formal P vs NP statement without a separate proof that the machine models agree.

For TM2 composition, an independent Mathlib pull request ([#44441](https://github.com/leanprover-community/mathlib4/pull/44441)) was open at the time of writing.

## How this was made

The Lean code was written by an AI coding agent (Claude Code, by Anthropic) over a series of scoped sessions that I directed. For each session I set the goal and the rules (no `sorry`, `axiom`, `native\_decide`, or environment-modifying metaprogramming in proved code; statements written down before proving them), reviewed the session's report, and independently ran the build, axiom, and `leanchecker` checks described above. `NOTES.md` records the development session by session.

## Versions

* Lean v4.31.0
* Mathlib v4.31.0 (`fabf563a`)
* LeanMillenniumPrizeProblems `603053d` (Git submodule)
* Physlib `3dddd61e`

## License

Copyright 2026 Joshua Tan. Licensed under the Apache License, Version 2.0; see `LICENSE`. LeanMillenniumPrizeProblems, Mathlib and Physlib are separate projects under their own licenses.

