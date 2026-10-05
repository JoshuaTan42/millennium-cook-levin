## PHASE 4 (2026-10-05): falsification of C3 (SDCL*) exactly as pre-registered in PHASE3.md 2.3.8 / Appendix C

Everything below was written **before the first measured run of SDCL\***. Nothing in PHASE3.md was changed.
Python/C++ output is evidence, never proof.

### lean4checker (reported by the user, not run this session)
The user reports that lean4checker has been run on every module and with `--fresh` on `Solution`, all passing. This supersedes the
"lean4checker: not run" lines above (2026-10-05 checks section and earlier). Not run by me this session; recorded as reported.
`sat_in_p` is still `sorry`, so the project status is unchanged: **NOT PROVED**.

### Definitions checked against the papers (PHASE3.md 2.3.1 asked for this before experiments)
Sources read in full: HKSB17 "PRuning Through Satisfaction" (HVC 2017, text extracted from the PDF) and HKB19 "Encoding Redundancy
for Satisfaction-Driven Clause Learning" (TACAS 2019). Discrepancies found:

1. **Positive reduct**: HKB19 Definition 3: `p_alpha(F) = G ∧ C`, `C` the clause that blocks `alpha`, `G = {touched_alpha(D) | D ∈ F and D|alpha = ⊤}`.
   Identical to PHASE3.md 2.3.1. No discrepancy.
2. **Filtered positive reduct**: HKB19 Definition 4: `f_alpha(F) = G ∧ C` with `G = {touched_alpha(D) | D ∈ F and F|alpha ⊬₁ untouched_alpha(D)}`.
   PHASE3.md restates it as "drop from `p(F, alpha)` the clauses `D` whose untouched part is unit-implied by `F|alpha`". The paper's definition
   ranges over all `D ∈ F`, but the paper itself proves (right after Def. 4) that every clause not satisfied by `alpha` is filtered, so the two
   formulations coincide. No discrepancy. Implementation: for each clause `D` of the *current* formula (original plus learnt, HKB19 and SaDiCaL
   both use the current clause database) satisfied by `alpha`, assume the negations of its unassigned literals at a temporary decision level,
   unit-propagate, and drop `D` iff a conflict results; clauses with no unassigned literal are kept (`F|alpha ⊢₁ ⊥` is false since `alpha` is consistent).
3. **Learned clause**: PHASE3.md 2.3.2 says "learn the clause `¬alpha` as a PR clause with witness `omega` ... backjump to the asserting level".
   Both papers learn the clause that blocks the *decision* literals only (HKSB17 Theorem 3 and Fig. 1 `AnalyzeWitness`; HKB19 Sect. "Preliminaries":
   the clause "usually consists of the decision literals of the current assignment"); the clause blocking the whole trail is not asserting after a
   backjump, so the pre-registered "backjump to the asserting level" only makes sense for the decision-literal clause. **Implemented: learn
   `C = ¬(decision literals)`, PR w.r.t. the current formula with witness `omega` (HKSB17 Thm. 3; also checked directly: the earliest trail
   literal on which `omega` disagrees with `alpha` is a decision literal, because every propagated literal's reason clause is fully assigned and
   therefore present in the reduct).** The proof log records `C` with witness `omega` (DPR format) and every proof is checked independently.
4. **Witness `omega`**: the inner solver's complete model of the reduct, over exactly `var(alpha)` (the full trail including level 0). Same as the papers.
5. **When the reduct is checked**: PHASE3.md: before every decision at level >= 1. HKB19 (Sect. "Implementation"): SaDiCaL "computes the pruning
   predicate before every decision". Same. (No check when all variables are already assigned: there is no next decision; the formula is satisfied.)

### Implementation decision: own implementation, SaDiCaL does not match the pre-registered configuration
SaDiCaL (source `sadical.zip` from http://fmv.jku.at/sadical, version string `00n`, 4.9k lines of C incl. tests; built under WSL Ubuntu 22.04)
differs from SDCL\* in every base-CDCL parameter fixed in PHASE3.md 2.3.2:

| Component | SDCL\* (pre-registered) | SaDiCaL defaults (`internal.h` OPTIONS, `sadical.c`) |
|---|---|---|
| decision heuristic | VSIDS, decay 0.95, phase saving | VMTF queue plus dedicated look-ahead heuristics (`root`/`nonroot` = 3 "PHP": least-constrained literal at the root, smallest reduced clause elsewhere), witness-literal priority ("RELEVANT" mode), `autarky` heuristic |
| restarts | Luby, unit 100 conflicts | glue-based (fast/slow EMA, `restartmargin` 1.1, `restartint` 10), plus a forced restart after an "unbalanced prune" |
| learnt-clause reduction | every 2,000 conflicts, keep LBD <= 2 and most active half | `reduceinit` 2000, `reduceinc` 300 (growing interval), keep glue <= 3 or size <= 3 |
| conflict counting | real conflicts | a successful prune counts as a conflict (`prune()`: `INC_STATS (conflicts)`) |
| inner solver limit | 100 conflicts | no conflict limit on the inner solver found in the source (inner solver re-created per check) |
| pruning | at every level >= 1 | only at "look-ahead" decision levels, `level` <= 2000 |

Therefore SDCL\* was implemented from scratch (`phase4/src/sdcl.cpp`, C++17, 500 lines, MinGW g++ 13.1 `-O3 -static`) exactly as specified,
with the three variants `--mode=sdcl` (primary), `--mode=plain` (ablation i), `--mode=unfiltered` (ablation ii). SaDiCaL is run only as a
**supplementary reference** on the home-turf families; its numbers are reported separately and play no role in the kill criteria.

Implementation details fixed now (not in PHASE3.md, needed to run):
* Parsing: duplicate literals removed, tautological clauses dropped, SATLIB `%` end marker honoured; no other preprocessing.
* Schedule convention for "conflicts" in the restart and reduction schedules: see the dedicated paragraph below (SCHEDULE).
* Database reduction deletes the least active `floor(k/2)` of the `k` reducible learnt clauses (LBD > 2, size > 1, not a current reason).
* Inner solver: a fresh instance of the same CDCL code on the reduct mapped to `|alpha|` variables, `--inner-limit=100` conflicts, no SDCL step,
  no database reduction (unreachable below 2,000 conflicts), Luby restarts (unreachable below 100 conflicts).
* Exact memoisation inside one reduct build: the filter test for a single unassigned literal `u` (`F|alpha ⊢₁ (u)`?) is computed once per
  reduct build and reused for every satisfied clause whose untouched part is exactly `{u}`. Same answers, fewer propagations.
* Cost (pre-registered): `conflicts_outer + conflicts_inner + reduct_checks`, printed as `c stat cost`. PR learns, decisions, propagations,
  filter tests, filtered clauses, reduct sizes and wall-clock are also recorded.
* Proof log: DPR text; `d` lines for every deleted clause; final `0`. Checked with dpr-trim (Heule, github `marijnheule/dpr-trim`, commit
  `2dff405`, built with MinGW using `-Dgetc_unlocked=getc`) on every UNSAT answer, and with the own pure-Python checker `prcheck.py`
  (unit propagation only, no shared code) on every UNSAT proof up to 3 MB.
* Models checked by `check_model.py` (direct evaluation, no shared code) on every SAT answer; CaDiCaL 1.9.5 (PySAT 1.9.dev15, hard subprocess
  timeouts; PySAT's `interrupt()` does not stop CaDiCaL here) labels every F1/F2/F7 instance.

### Schedule convention (decided before any measured run)
SCHEDULE_PLACEHOLDER

### Instance generation (Appendix C) and manifest
Generator: `phase4/src/gen_instances.py` (CNFgen 0.9.6 for F1 random part, F2, F3, F4, F5; own scripts for F6 and F8; SATLIB files downloaded from
https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/). Choices not fixed by PHASE3.md:
* F1: `m = floor(4.26 n + 0.5)` (50→213, 75→320, 100→426, 125→533, 150→639, 175→746, 200→852, 225→959, 250→1065); CNFgen `RandomKCNF(3,n,m,seed)`,
  seeds 0–19; plus SATLIB `uf<n>-01..10` **and** `uuf<n>-01..10` (the sentence "first 10 SATLIB uf/uuf files" is read as 10 of each, so that
  both labels are present for K4). F2: `m = 5n`, seeds 0–9.
* F4: `networkx.random_regular_graph(3, n, seed)` seeds 0–9, CNFgen `TseitinFormula(G)` default charges (odd charge on the first vertex only,
  total charge odd, UNSAT regardless of connectivity; connectivity recorded in the file header).
* F5: CNFgen `CliqueColoring(n, k, k-1)` with `k = ceil(sqrt n)`.
* F6: `p, q` distinct `b`-bit primes with leading bit 1 (SAT) or `N` a random `2b`-bit prime (UNSAT), `random.Random(1000 b + seed)`, `sympy.isprime`;
  circuit: `b×b` AND partial products, rows accumulated by ripple-carry adders (full adder: 8 XOR3 + 6 majority clauses; half adder: 4 + 3),
  leading bits of `p, q` fixed by unit clauses, all `2b` output bits fixed by unit clauses. Circuit checked by unit-propagation simulation.
* F8: one variable per domino, exactly-one per cell (at-least-one plus pairwise at-most-one), corners (0,0) and (s-1,s-1) removed; variable
  and clause counts equal CNFgen's `MutilatedChessboard(s, s)` for every size.
* F7: GBD query `track=main_2023 and variables<=3000 and clauses<=30000` (90 of the 399 main-track instances; all 90 headers re-checked locally);
  CaDiCaL 1.9.5 with a 60 s wall-clock limit per instance (see the F7 list below for the machine conditions).

Total: 612 generated/copied instances plus the F7 selection. SHA-256 manifest: `phase4/instances/MANIFEST.jsonl` (612 lines, one per instance,
with family, size, variable/clause counts, label and generator parameters); the manifest's own hash and the per-family counts are:

MANIFEST_PLACEHOLDER

### Solver verification before any measurement (step 3 of the session instructions)
FUZZ_PLACEHOLDER

### F7 list (written before any SDCL\* run)
F7_PLACEHOLDER

### Environment
Windows 11 Pro 10.0.26200, 16 logical CPUs, 137 GB RAM, Python 3.11.9, PySAT 1.9.dev15 (CaDiCaL 1.9.5), CNFgen 0.9.6, networkx 3.2.1, sympy 1.14.0,
MinGW g++ 13.1.0 (CLion bundle), WSL Ubuntu 22.04 gcc 11.4 (SaDiCaL only). Runs are executed by `phase4/src/run_phase4.py` with 13 concurrent
single-threaded solver processes; wall-clock is therefore measured under moderate contention and is secondary (cost is the primary measure).
