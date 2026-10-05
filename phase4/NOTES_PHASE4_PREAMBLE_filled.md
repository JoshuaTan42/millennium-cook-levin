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
PHASE3.md 2.3.2 fixes "Luby restarts with unit 100 conflicts" and "learned-clause database reduction every 2,000 conflicts". In SDCL mode
the database also receives PR clauses, which are not produced by conflicts, so the text admits two readings: (L) literal: only real
conflicts advance the restart and reduction schedules (PR clauses accumulate between conflicts); (S) SaDiCaL's convention: a successful
prune counts as a conflict for both schedules (`prune()` does `INC_STATS (conflicts)`). The implementation has both (`--prunes-as-conflicts`
selects S). Before any measured run both were compared on the smoke/fuzz instances (`phase4/results/schedule_compare.log`, 120 s limit for
the fuzz cases, 900 s otherwise; wall-clock under light load):

| instance | L: cost / wall / outcome | S: cost / wall / outcome |
|---|---|---|
| fuzz seed0 case35 (clique-colouring 7,2,3; satisfiable; plain CDCL cost 13, 2 ms) | 30,005 / 120 s / UNKNOWN (2 real conflicts, 4,071 PR clauses, 0 reductions) | 23,403 / 120 s / UNKNOWN (15 conflicts, 5,758 PR clauses, 2 reductions, 29 restarts) |
| fuzz seed0 case92 (clique-colouring 8,2,3; satisfiable; plain cost 14) | 23,524 / 120 s / UNKNOWN | 19,967 / 120 s / UNKNOWN |
| F3 `php_9_8` | 14,130 / 40 s / UNSAT | 33,827 / 99 s / UNSAT |
| F8 `mchess_8` | 2,030 / 1.9 s / UNSAT | 2,016 / 2.3 s / UNSAT |

The pathology that motivated looking at S (thousands of PR clauses learned on a trivially satisfiable formula without finding a model) is
present under both readings, so S does not remove it; S is worse on PHP and equal on the chessboard. **Decision: reading L (literal) is the
pre-registered SDCL\*, used for every measured run; S is not run.** An earlier smoke run of `php_9_8` under S (during development, heavier
machine load) gave cost 35,426 / 183 s; it is superseded by the table above. The reported cost is in all cases the pre-registered
`conflicts_outer + conflicts_inner + reduct_checks` with `conflicts_outer` = real conflicts.

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

| family | instances | sizes | labels |
|---|---|---|---|
| F1 | 360 | 50, 75, 100, 125, 150, 175, 200, 225, 250 | cadical: 360 |
| F2 | 70 | 100, 150, 200, 250, 300, 350, 400 | cadical: 70 |
| F3 | 9 | 8, 10, 12, 14, 16, 20, 25, 30, 40 | UNSAT: 9 |
| F4 | 80 | 20, 40, 60, 80, 100, 150, 200, 300 | UNSAT: 80 |
| F5 | 7 | 8, 10, 12, 16, 20, 25, 30 | UNSAT: 7 |
| F6 | 80 | 6, 8, 10, 12, 14, 16, 18, 20 | SAT: 40, UNSAT: 40 |
| F8 | 6 | 6, 8, 10, 12, 14, 16 | UNSAT: 6 |

SHA-256 of `phase4/instances/MANIFEST.jsonl`: `c22c31cf176552edf4e580c7cde3f938f801abad4e0aec9ed99a3eedfe21c1fe`. Full per-instance hash list: `phase4/instances/MANIFEST.sha256` (written now).
CaDiCaL labels for F1/F2 (`labels_f12.jsonl`, 1800 s limit, 6 concurrent): F1 SAT: 191, F1 UNSAT: 169, F2 TIMEOUT: 4, F2 UNSAT: 66. The F2 n=400 timeouts are being re-run with a 7200 s limit (`labels_retry.jsonl`); instances without a label are reported as unlabelled, never counted as agreeing.

### Solver verification before any measurement (step 3 of the session instructions)
* seed 0: 150 cases (30 SAT, 120 UNSAT by CaDiCaL), every answer of all three modes agreed with CaDiCaL 1.9.5, every model was accepted by `check_model.py`, every UNSAT proof was accepted by dpr-trim. Flagged lines: 3.
  - `CASE 17 (mchess 2x2): PROBLEMS ['sdcl: prcheck.py did not verify: FAIL line 1: empty clause not RUP', 'plain: prcheck.py did not verify: FAIL line 1: empty clause not RUP', 'unfiltered: prcheck.py did not verify: FAIL line 1: empty clause not RUP']`
  - `CASE 35 (cliquecol 7 2 3): PROBLEMS ['sdcl: status UNKNOWN (rc=0) after 120.3s']`
  - `CASE 92 (cliquecol 8 2 3): PROBLEMS ['sdcl: status UNKNOWN (rc=0) after 120.2s', 'unfiltered: status UNKNOWN (rc=0) after 120.2s']`
* seed 1: 150 cases (32 SAT, 118 UNSAT by CaDiCaL), every answer of all three modes agreed with CaDiCaL 1.9.5, every model was accepted by `check_model.py`, every UNSAT proof was accepted by dpr-trim. Flagged lines: 1.
  - `CASE 101 (cliquecol 8 4 4): PROBLEMS ['sdcl: status UNKNOWN (rc=0) after 120.2s', 'unfiltered: status UNKNOWN (rc=0) after 120.2s']`
* Interpretation of the flags: the `prcheck.py` failures on `mchess 2x2` were a bug in the own checker (a formula containing empty clauses; fixed, the three proofs re-verify); the `status UNKNOWN after 120 s` lines are SDCL\*/unfiltered exceeding the fuzz time limit on small satisfiable clique-colouring formulas that plain CDCL solves in 2 ms (cost 13) — not wrong answers, but recorded here because they are the first sign of the behaviour discussed under "schedule convention" below. An earlier fuzz attempt whose two seeds shared one scratch directory produced spurious "wrong answer" lines (files overwritten mid-run); all of those cases were re-run on the actual files and agreed with CaDiCaL with verified proofs.
* Smoke tests on pre-registered instances (not measurements): `php_9_8` UNSAT in all three modes, proofs verified by dpr-trim and by `prcheck.py`; `uf50-01` SAT with verified model; `uuf50-01` UNSAT.

### F7 list (written before any SDCL\* run)
Selection rule (PHASE3.md): GBD `track=main_2023`, `variables<=3000`, `clauses<=30000` (90 instances; every header re-checked locally: all 90 within bounds), CaDiCaL 1.9.5 solves within 60 s wall-clock. Two labelling passes were run: pass 1 under heavy CPU contention (8 CaDiCaL processes beside fuzzing and other labelling; 14 solved), pass 2 on a quiet machine with 4 concurrent CaDiCaL processes (15 solved). **Pass 2 is the F7 selection.** All 90 outcomes of both passes are in `phase4/instances/sc23/labels_f7.jsonl` (pass 2) and `labels_f7_contended_pass1.jsonl` (pass 1).

| # | GBD hash | original name | vars | clauses | CaDiCaL (pass 2) | time (s) | pass 1 |
|---|---|---|---|---|---|---|---|
| 1 | `02066c116dbacc40ec5cca2067db26c0` | mrpp_4x4_12_12 | 2672 | 16408 | UNSAT | 54.8 | TIMEOUT |
| 2 | `0297c2a35f116ffd5382aea5b421e6df` | Urquhart-s3-b3.shuffled-as.sat03-1556 | 45 | 376 | UNSAT | 28.8 | UNSAT |
| 3 | `037c423f56548082b1935e88c48ffdda` | 3col120_5_2.shuffled | 240 | 1026 | SAT | 2.7 | SAT |
| 4 | `03de316ba1e90305471a3b8620cb9cd7` | satsgi-n23himBHm26-p0-q248 | 598 | 14076 | SAT | 0.1 | SAT |
| 5 | `17039a3ed02ea12653ec5389e56dab50` | pbl-00070.shuffled-as.sat05-1324.shuffled-as.sat05-1324 | 257 | 7375 | UNSAT | 1.4 | UNSAT |
| 6 | `211938776d92f11870a687abd11d55a4` | iso-icl004.shuffled-as.sat05-3238 | 1001 | 9897 | UNSAT | 0.1 | UNSAT |
| 7 | `24b93d0bf941e4b050c9109e4cb7faf4` | connm-ue-csp-sat-n600-d-0.02-s1022905465.used-as.sat04-951 | 556 | 6427 | SAT | 4.6 | SAT |
| 8 | `27b4fe4cb0b4e2fd8327209ca5ff352c` | grid_10_20.shuffled | 398 | 741 | UNSAT | 0.1 | UNSAT |
| 9 | `28f29fe949422ec88892e18073de065c` | 5col100_15_6.shuffled | 300 | 4059 | UNSAT | 41.8 | UNSAT |
| 10 | `36c342091848d5d6a1a8eeb3a8b49b86` | rovers1_ks99i.renamed-as.sat05-3971 | 439 | 5423 | SAT | 0.1 | SAT |
| 11 | `571a2f223784fb92a53b4cc8cc8b569e` | clqcolor-08-06-07.shuffled-as.sat05-1257 | 132 | 1527 | UNSAT | 43.8 | UNSAT |
| 12 | `587150fb7b12a6b5dd7e4a9446b9713b` | iso-ukn004.shuffled-as.sat05-3385 | 1890 | 12666 | SAT | 0.4 | SAT |
| 13 | `70af2c3bfd44bcf9baa2a9605f4a17fe` | gensys-icl002.shuffled-as.sat05-2714 | 1444 | 7479 | UNSAT | 35.6 | UNSAT |
| 14 | `911cbc796d15eb316d36c82c90fd7d11` | c499_gr_2pin_w6.shuffled | 2070 | 22470 | SAT | 1.3 | SAT |
| 15 | `fe19a31b76cbba5901e16ce36c7578ed` | C208_FA_UT_3254 | 1805 | 7334 | UNSAT | 0.1 | UNSAT |

Instances solved in pass 1 but not in pass 2 (excluded by the rule, listed for transparency): none.

### Environment
Windows 11 Pro 10.0.26200, 16 logical CPUs, 137 GB RAM, Python 3.11.9, PySAT 1.9.dev15 (CaDiCaL 1.9.5), CNFgen 0.9.6, networkx 3.2.1, sympy 1.14.0,
MinGW g++ 13.1.0 (CLion bundle), WSL Ubuntu 22.04 gcc 11.4 (SaDiCaL only). Runs are executed by `phase4/src/run_phase4.py` with 13 concurrent
single-threaded solver processes; wall-clock is therefore measured under moderate contention and is secondary (cost is the primary measure).
