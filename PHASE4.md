# PHASE4.md — Falsification of candidate C3 (SDCL\*, satisfaction-driven clause learning with PR learning)

Session 2026-10-05/06. Pre-registered plan: PHASE3.md §2.3.8 and Appendix C, run exactly as written (no configuration, family, size, count or
kill criterion changed). Everything written before the first measured run is in NOTES.md ("PHASE 4 (2026-10-05)" section): definitions checked
against the papers, implementation decisions, instance manifest with SHA-256 hashes, solver verification, and the F7 list. Project status is
unchanged: **NOT PROVED** (`PvsNP.sat_in_p` is still `sorry`). Python/C++ output is evidence, never proof. Nothing is committed.

Report generated 2026-10-06 09:11 from `phase4/results/runs.jsonl` (536 of 1881 planned runs recorded).

## 1. Implementation used

**Own implementation of SDCL\* (`phase4/src/sdcl.cpp`), not the authors' SaDiCaL.** The original SDCL implementation by Kiesl, Heule and Biere
(SaDiCaL, `http://fmv.jku.at/sadical`, version string `00n`) exists and was downloaded, built (WSL Ubuntu 22.04, gcc 11.4) and run, but it does
**not** match the pre-registered configuration in any base-CDCL parameter: it uses a VMTF queue plus dedicated look-ahead decision heuristics
(least-constrained literal at the root, smallest reduced clause elsewhere, witness-literal priority), glue-based restarts, a growing reduction
interval keeping glue ≤ 3 / size ≤ 3, counts prunes as conflicts, has no conflict limit on the inner solver, and prunes only at look-ahead levels
(details and source line references in NOTES.md). PHASE3.md fixes VSIDS 0.95 with phase saving, Luby restarts (unit 100), 1-UIP with
minimisation, reduction every 2,000 conflicts keeping LBD ≤ 2 plus the most active half, no preprocessing, a reduct check before every decision at
level ≥ 1, and an inner plain-CDCL limited to 100 conflicts. SDCL\* was therefore implemented from scratch (C++17, ~520 lines, MinGW g++ 13.1 `-O3`),
with the three pre-registered variants: `sdcl` (filtered positive reduct, primary), `plain` (ablation i: SDCL step disabled), `unfiltered`
(ablation ii: original positive reduct). SaDiCaL was run only as a **supplementary reference** on the home-turf families (§7); it plays no role in the
kill criteria.

Definitions (NOTES.md has the full check): positive and filtered positive reducts exactly as HKB19 Definitions 3 and 4; the learned clause is the
negation of the decision literals (HKSB17 Thm. 3 / Fig. 1, HKB19 preliminaries), which is the asserting clause the pre-registration backjumps on;
the witness is the inner solver's model of the reduct over the full trail. Implementation choices not fixed by PHASE3.md and decided before measuring:
duplicate-literal/tautology removal at parse time only; the reduct is built from the current formula (original plus learnt clauses); an exact
per-reduct memoisation of single-literal filter tests; and the schedule convention below.

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

**Addendum (written after the measured runs had started; nothing changed).** The last comparison run, F4 `tseitin_n40_s0` (60 variables, 160 clauses),
finished after the launch: L: 35,465 cost / 900 s limit reached / UNKNOWN (0 real conflicts, 10,334 PR clauses, 0 reductions, 0 restarts);
S: 36,282 cost / 348 s / UNSAT (26 conflicts, 5 reductions). The costs are the same to within 3%; the wall-clock differs because under L the
database grows without bound between real conflicts (every reduct check filters every stored PR clause). Under the no-change rule of Appendix C
the measured runs stay with L; the reader should keep in mind that cap hits (K2, K5) under L are partly a wall-clock effect of the unbounded
database, while the pre-registered cost measure is essentially unaffected by the choice on this instance.

**Cost measure** (pre-registered): `conflicts_outer + conflicts_inner + reduct_checks`; wall-clock secondary; cap 3,600 s per run (solver's own
limit; hard kill at 3,700 s). Timeouts are censored: the solver prints its statistics at the cap, so a timed-out run's cost is a lower bound and
medians over sizes containing timeouts are reported as `>=` (censored) and excluded from the fits (Appendix C).

**Verification** (every run, before counting it): SAT answers are evaluated by `check_model.py` (independent evaluator, no shared code);
UNSAT answers are checked by dpr-trim (Heule's DPR checker, commit `2dff405`) on the solver's DPR proof log, and additionally by the own
pure-Python checker `prcheck.py` on proofs up to 3 MB; every F1/F2/F7 instance is labelled by CaDiCaL 1.9.5 (PySAT) with hard subprocess
timeouts; F3–F6 and F8 labels are known by construction. Before any measurement the solver was fuzzed on 300 random and structured formulas against
CaDiCaL (NOTES.md): no disagreement, every model and every proof verified.

## 2. Environment

Windows 11 Pro 10.0.26200, 16 logical CPUs, 137 GB RAM; Python 3.11.9, PySAT 1.9.dev15 (CaDiCaL 1.9.5), CNFgen 0.9.6, networkx 3.2.1, sympy 1.14.0;
MinGW g++ 13.1.0; WSL Ubuntu 22.04 (SaDiCaL only). Driver `phase4/src/run_phase4.py`, 13 concurrent single-threaded solver processes plus
verification, labelling and SaDiCaL jobs on the same machine: wall-clock numbers are under contention (secondary measure).

## 3. Completion status of the pre-registered run plan

| mode | jobs recorded | of | solved | timeouts | crashes |
|---|---|---|---|---|---|
| sdcl | 286 | 627 | 213 | 73 | 0 |
| plain | 250 | 627 | 225 | 25 | 0 |
| unfiltered | 0 | 627 | 0 | 0 | 0 |

Order of execution (the only thing changed after the first measured run; configuration, instances and criteria are untouched): the first 331 runs in
size order across all families (SDCL\* and plain). After two checkpoints showed one 13-job batch per hour at the cap (about 85 h for the full plan),
the driver was restarted in staged priority (F3 F4 F5 F8; then the F1 UNSAT instances at n = 200–250 needed by K4; then F6 F2 F7; then the rest of
F1; the unfiltered ablation last) and, from 02:47, in breadth-first rounds (the first instance of every family × size × label × mode group before
the second instance of any group). At each of the three restarts the in-flight runs were killed and later re-run from scratch; killed attempts were
never recorded, so every recorded run is a first completion. Runs not recorded at the stop point (09:08 local) are shown as `(not run)` in the
tables below, never as solved or failed.

## 4. Results per family, fits and kill criteria (generated by `phase4/src/analyze.py`)


Runs recorded: 536. Modes: ['plain', 'sdcl'].

### K1 (wrong answer / rejected proof)

**K1 fired: NO** (0 wrong answers or rejected proofs; 0 crashes recorded separately)


Verification tally: {"sat_total": 166, "model_verified": 166, "sat_label_agrees": 166, "unsat_total": 272, "dprtrim_verified": 269, "prcheck_verified": 219, "label_agrees": 272, "dprtrim_checker_timeout_1h": 3}

UNSAT answers whose dpr-trim check exceeded the checker's own 3,600 s limit (checker timeouts, not rejections; the answers agree with the construction label or the CaDiCaL label):
- F3 php_11_10.cnf [plain]: cost 8168962, expected UNSAT
- F4 tseitin_n80_s0.cnf [plain]: cost 23780106, expected UNSAT
- F8 mchess_14.cnf [plain]: cost 15093324, expected UNSAT

### F1

| size | mode | n | solved | timeouts | crashes | answers verified | label agrees | median cost | max cost | median wall (s) |
|---|---|---|---|---|---|---|---|---|---|---|
| 50 | sdcl | 40 | 40 | 0 | 0 | 40 | 40 | 197 | 1016 | 0.4 |
| 50 | plain | 40 | 40 | 0 | 0 | 40 | 40 | 40 | 125 | 0.2 |
| 75 | sdcl | 40 | 40 | 0 | 0 | 40 | 40 | 665 | 7623 | 0.7 |
| 75 | plain | 40 | 40 | 0 | 0 | 40 | 40 | 132 | 288 | 0.2 |
| 100 | sdcl | 39 | 39 | 0 | 0 | 39 | 39 | 1599 | 5634 | 1.6 |
| 200 | sdcl | 3 | 3 | 0 | 0 | 3 | 3 | 82650 | 130704 | 1702.6 |
| 200 | plain | 3 | 3 | 0 | 0 | 3 | 3 | 24506 | 40343 | 3.9 |
| 225 | sdcl | 3 | 1 | 2 | 0 | 1 | 1 | >= 145349 (censored) | 121737 | 2719.3 |
| 225 | plain | 3 | 3 | 0 | 0 | 3 | 3 | 38449 | 68593 | 10.7 |
| 250 | sdcl | 3 | 0 | 3 | 0 | 0 | 0 | >= 125920 (censored) | - | - |
| 250 | plain | 3 | 3 | 0 | 0 | 3 | 3 | 201619 | 612671 | 40.3 |

### F2

| size | mode | n | solved | timeouts | crashes | answers verified | label agrees | median cost | max cost | median wall (s) |
|---|---|---|---|---|---|---|---|---|---|---|
| 100 | sdcl | 10 | 10 | 0 | 0 | 10 | 10 | 842 | 1217 | 1.3 |
| 100 | plain | 10 | 10 | 0 | 0 | 10 | 10 | 280 | 418 | 0.3 |
| 150 | sdcl | 10 | 10 | 0 | 0 | 10 | 10 | 3164 | 4696 | 9.8 |
| 150 | plain | 10 | 10 | 0 | 0 | 10 | 10 | 1000 | 1630 | 0.3 |
| 200 | sdcl | 4 | 4 | 0 | 0 | 4 | 4 | 12172 | 16088 | 93.2 |
| 200 | plain | 3 | 3 | 0 | 0 | 3 | 3 | 4212 | 4832 | 0.6 |
| 250 | sdcl | 3 | 3 | 0 | 0 | 3 | 3 | 90969 | 109182 | 2015.9 |
| 250 | plain | 3 | 3 | 0 | 0 | 3 | 3 | 36594 | 39910 | 4.1 |
| 300 | sdcl | 2 | 0 | 2 | 0 | 0 | 0 | >= 129509 (censored) | - | - |
| 300 | plain | 3 | 3 | 0 | 0 | 3 | 3 | 467077 | 528939 | 100.0 |
| 350 | sdcl | 2 | 0 | 2 | 0 | 0 | 0 | >= 133413 (censored) | - | - |
| 350 | plain | 2 | 2 | 0 | 0 | 2 | 2 | 809776 | 1121550 | 185.9 |
| 400 | sdcl | 4 | 0 | 4 | 0 | 0 | 0 | >= 124268 (censored) | - | - |
| 400 | plain | 4 | 3 | 1 | 0 | 3 | 3 | 9532322 | 11179657 | 2308.9 |

### F3

| size | mode | n | solved | timeouts | crashes | answers verified | label agrees | median cost | max cost | median wall (s) |
|---|---|---|---|---|---|---|---|---|---|---|
| 8 | sdcl | 1 | 1 | 0 | 0 | 1 | 1 | 14130 | 14130 | 53.1 |
| 8 | plain | 1 | 1 | 0 | 0 | 1 | 1 | 19726 | 19726 | 6.5 |
| 10 | sdcl | 1 | 0 | 1 | 0 | 0 | 0 | >= 182458 (censored) | - | - |
| 10 | plain | 1 | 1 | 0 | 0 | 0 | 1 | 8168962 | 8168962 | 2955.8 |
| 12 | sdcl | 1 | 0 | 1 | 0 | 0 | 0 | >= 299581 (censored) | - | - |
| 12 | plain | 1 | 0 | 1 | 0 | 0 | 0 | >= 6962048 (censored) | - | - |
| 14 | sdcl | 1 | 0 | 1 | 0 | 0 | 0 | >= 296040 (censored) | - | - |
| 14 | plain | 1 | 0 | 1 | 0 | 0 | 0 | >= 5294080 (censored) | - | - |
| 16 | sdcl | 1 | 0 | 1 | 0 | 0 | 0 | >= 511245 (censored) | - | - |
| 16 | plain | 1 | 0 | 1 | 0 | 0 | 0 | >= 4174144 (censored) | - | - |
| 20 | sdcl | 1 | 0 | 1 | 0 | 0 | 0 | >= 193282 (censored) | - | - |
| 20 | plain | 1 | 0 | 1 | 0 | 0 | 0 | >= 2854016 (censored) | - | - |
| 25 | sdcl | 1 | 0 | 1 | 0 | 0 | 0 | >= 150945 (censored) | - | - |
| 25 | plain | 1 | 0 | 1 | 0 | 0 | 0 | >= 2786240 (censored) | - | - |
| 30 | sdcl | 1 | 0 | 1 | 0 | 0 | 0 | >= 96887 (censored) | - | - |
| 30 | plain | 1 | 0 | 1 | 0 | 0 | 0 | >= 2507520 (censored) | - | - |
| 40 | sdcl | 1 | 0 | 1 | 0 | 0 | 0 | >= 81482 (censored) | - | - |
| 40 | plain | 1 | 0 | 1 | 0 | 0 | 0 | >= 1862016 (censored) | - | - |

### F4

| size | mode | n | solved | timeouts | crashes | answers verified | label agrees | median cost | max cost | median wall (s) |
|---|---|---|---|---|---|---|---|---|---|---|
| 20 | sdcl | 10 | 10 | 0 | 0 | 10 | 10 | 1612 | 3128 | 2.1 |
| 20 | plain | 10 | 10 | 0 | 0 | 10 | 10 | 187 | 436 | 0.3 |
| 40 | sdcl | 10 | 0 | 10 | 0 | 0 | 0 | >= 51111 (censored) | - | - |
| 40 | plain | 10 | 10 | 0 | 0 | 10 | 10 | 2087 | 7684 | 0.4 |
| 60 | sdcl | 10 | 0 | 10 | 0 | 0 | 0 | >= 48135 (censored) | - | - |
| 60 | plain | 9 | 9 | 0 | 0 | 9 | 9 | 55989 | 491260 | 4.6 |
| 80 | sdcl | 3 | 0 | 3 | 0 | 0 | 0 | >= 70709 (censored) | - | - |
| 80 | plain | 3 | 3 | 0 | 0 | 2 | 3 | 5129420 | 23780106 | 593.6 |
| 100 | sdcl | 3 | 0 | 3 | 0 | 0 | 0 | >= 58817 (censored) | - | - |
| 100 | plain | 3 | 0 | 3 | 0 | 0 | 0 | >= 24570368 (censored) | - | - |
| 150 | sdcl | 3 | 0 | 3 | 0 | 0 | 0 | >= 43099 (censored) | - | - |
| 150 | plain | 3 | 0 | 3 | 0 | 0 | 0 | >= 17000000 (censored) | - | - |
| 200 | sdcl | 3 | 0 | 3 | 0 | 0 | 0 | >= 56633 (censored) | - | - |
| 200 | plain | 3 | 0 | 3 | 0 | 0 | 0 | >= 14884032 (censored) | - | - |
| 300 | sdcl | 3 | 0 | 3 | 0 | 0 | 0 | >= 40944 (censored) | - | - |
| 300 | plain | 3 | 0 | 3 | 0 | 0 | 0 | >= 11842048 (censored) | - | - |

### F5

| size | mode | n | solved | timeouts | crashes | answers verified | label agrees | median cost | max cost | median wall (s) |
|---|---|---|---|---|---|---|---|---|---|---|
| 8 | sdcl | 1 | 1 | 0 | 0 | 1 | 1 | 6194 | 6194 | 9.7 |
| 8 | plain | 1 | 1 | 0 | 0 | 1 | 1 | 1195 | 1195 | 0.3 |
| 10 | sdcl | 1 | 0 | 1 | 0 | 0 | 0 | >= 66020 (censored) | - | - |
| 10 | plain | 1 | 1 | 0 | 0 | 1 | 1 | 61591 | 61591 | 4.7 |
| 12 | sdcl | 1 | 0 | 1 | 0 | 0 | 0 | >= 61225 (censored) | - | - |
| 12 | plain | 1 | 1 | 0 | 0 | 1 | 1 | 124801 | 124801 | 11.8 |
| 16 | sdcl | 1 | 0 | 1 | 0 | 0 | 0 | >= 60314 (censored) | - | - |
| 16 | plain | 1 | 1 | 0 | 0 | 1 | 1 | 642682 | 642682 | 76.0 |
| 20 | sdcl | 1 | 0 | 1 | 0 | 0 | 0 | >= 60626 (censored) | - | - |
| 20 | plain | 1 | 0 | 1 | 0 | 0 | 0 | >= 23258048 (censored) | - | - |
| 25 | sdcl | 1 | 0 | 1 | 0 | 0 | 0 | >= 57519 (censored) | - | - |
| 25 | plain | 1 | 0 | 1 | 0 | 0 | 0 | >= 20204032 (censored) | - | - |
| 30 | sdcl | 1 | 0 | 1 | 0 | 0 | 0 | >= 54831 (censored) | - | - |
| 30 | plain | 1 | 0 | 1 | 0 | 0 | 0 | >= 16475328 (censored) | - | - |

### F6

| size | mode | n | solved | timeouts | crashes | answers verified | label agrees | median cost | max cost | median wall (s) |
|---|---|---|---|---|---|---|---|---|---|---|
| 6 | sdcl | 10 | 10 | 0 | 0 | 10 | 10 | 52 | 111 | 0.4 |
| 6 | plain | 10 | 10 | 0 | 0 | 10 | 10 | 18 | 42 | 0.2 |
| 8 | sdcl | 10 | 10 | 0 | 0 | 10 | 10 | 232 | 498 | 0.7 |
| 8 | plain | 10 | 10 | 0 | 0 | 10 | 10 | 79 | 167 | 0.2 |
| 10 | sdcl | 6 | 6 | 0 | 0 | 6 | 6 | 1281 | 2057 | 3.9 |
| 10 | plain | 6 | 6 | 0 | 0 | 6 | 6 | 217 | 440 | 0.2 |
| 12 | sdcl | 6 | 6 | 0 | 0 | 6 | 6 | 3309 | 7285 | 14.6 |
| 12 | plain | 6 | 6 | 0 | 0 | 6 | 6 | 730 | 1676 | 0.4 |
| 14 | sdcl | 6 | 6 | 0 | 0 | 6 | 6 | 13387 | 20345 | 177.0 |
| 14 | plain | 6 | 6 | 0 | 0 | 6 | 6 | 1872 | 4734 | 0.9 |
| 16 | sdcl | 5 | 5 | 0 | 0 | 5 | 5 | 38119 | 67121 | 1001.7 |
| 16 | plain | 6 | 6 | 0 | 0 | 6 | 6 | 9596 | 25292 | 4.1 |
| 18 | sdcl | 4 | 3 | 1 | 0 | 3 | 3 | 79112 | 91340 | 2493.9 |
| 18 | plain | 6 | 6 | 0 | 0 | 6 | 6 | 33483 | 88386 | 16.0 |
| 20 | sdcl | 4 | 0 | 4 | 0 | 0 | 0 | >= 80574 (censored) | - | - |
| 20 | plain | 4 | 4 | 0 | 0 | 4 | 4 | 845542 | 1372237 | 564.0 |

### F7

| size | mode | n | solved | timeouts | crashes | answers verified | label agrees | median cost | max cost | median wall (s) |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | sdcl | 5 | 2 | 3 | 0 | 2 | 2 | >= 63437 (censored) | 210413 | 1023.9 |
| 0 | plain | 6 | 5 | 1 | 0 | 5 | 5 | 17288 | 3471978 | 1.7 |

### F8

| size | mode | n | solved | timeouts | crashes | answers verified | label agrees | median cost | max cost | median wall (s) |
|---|---|---|---|---|---|---|---|---|---|---|
| 6 | sdcl | 1 | 1 | 0 | 0 | 1 | 1 | 104 | 104 | 0.3 |
| 6 | plain | 1 | 1 | 0 | 0 | 1 | 1 | 54 | 54 | 0.1 |
| 8 | sdcl | 1 | 1 | 0 | 0 | 1 | 1 | 2030 | 2030 | 3.8 |
| 8 | plain | 1 | 1 | 0 | 0 | 1 | 1 | 958 | 958 | 0.3 |
| 10 | sdcl | 1 | 1 | 0 | 0 | 1 | 1 | 25851 | 25851 | 611.6 |
| 10 | plain | 1 | 1 | 0 | 0 | 1 | 1 | 6146 | 6146 | 0.8 |
| 12 | sdcl | 1 | 0 | 1 | 0 | 0 | 0 | >= 50885 (censored) | - | - |
| 12 | plain | 1 | 1 | 0 | 0 | 1 | 1 | 81855 | 81855 | 14.0 |
| 14 | sdcl | 1 | 0 | 1 | 0 | 0 | 0 | >= 43780 (censored) | - | - |
| 14 | plain | 1 | 1 | 0 | 0 | 0 | 1 | 15093324 | 15093324 | 3221.6 |
| 16 | sdcl | 1 | 0 | 1 | 0 | 0 | 0 | >= 86542 (censored) | - | - |
| 16 | plain | 1 | 0 | 1 | 0 | 0 | 0 | >= 13932736 (censored) | - | - |

### K2 (home-turf exponential signature, SDCL*, families F3 F4 F5 F8)


#### F3 (second-largest listed size: 30)

| size | median cost (SDCL*) | local exponent e_k | cap hit |
|---|---|---|---|
| 8 | 14130 | - | no |
| 10 | >= 182458 | - | YES (1/1) |
| 12 | >= 299581 | - | YES (1/1) |
| 14 | >= 296040 | - | YES (1/1) |
| 16 | >= 511245 | - | YES (1/1) |
| 20 | >= 193282 | - | YES (1/1) |
| 25 | >= 150945 | - | YES (1/1) |
| 30 | >= 96887 | - | YES (1/1) |
| 40 | >= 81482 | - | YES (1/1) |

#### F4 (second-largest listed size: 200)

| size | median cost (SDCL*) | local exponent e_k | cap hit |
|---|---|---|---|
| 20 | 1612 | - | no |
| 40 | >= 51111 | - | YES (10/10) |
| 60 | >= 48135 | - | YES (10/10) |
| 80 | >= 70709 | - | YES (3/3) |
| 100 | >= 58817 | - | YES (3/3) |
| 150 | >= 43099 | - | YES (3/3) |
| 200 | >= 56633 | - | YES (3/3) |
| 300 | >= 40944 | - | YES (3/3) |

#### F5 (second-largest listed size: 25)

| size | median cost (SDCL*) | local exponent e_k | cap hit |
|---|---|---|---|
| 8 | 6194 | - | no |
| 10 | >= 66020 | - | YES (1/1) |
| 12 | >= 61225 | - | YES (1/1) |
| 16 | >= 60314 | - | YES (1/1) |
| 20 | >= 60626 | - | YES (1/1) |
| 25 | >= 57519 | - | YES (1/1) |
| 30 | >= 54831 | - | YES (1/1) |

#### F8 (second-largest listed size: 14)

| size | median cost (SDCL*) | local exponent e_k | cap hit |
|---|---|---|---|
| 6 | 104 | - | no |
| 8 | 2030 | 10.33 | no |
| 10 | 25851 | 11.40 | no |
| 12 | >= 50885 | - | YES (1/1) |
| 14 | >= 43780 | - | YES (1/1) |
| 16 | >= 86542 | - | YES (1/1) |

**K2 fired: YES**

- F3: cap hit at size 10 (<= second-largest 30): 1 of 1 runs
- F3: cap hit at size 12 (<= second-largest 30): 1 of 1 runs
- F3: cap hit at size 14 (<= second-largest 30): 1 of 1 runs
- F3: cap hit at size 16 (<= second-largest 30): 1 of 1 runs
- F3: cap hit at size 20 (<= second-largest 30): 1 of 1 runs
- F3: cap hit at size 25 (<= second-largest 30): 1 of 1 runs
- F3: cap hit at size 30 (<= second-largest 30): 1 of 1 runs
- F4: cap hit at size 40 (<= second-largest 200): 10 of 10 runs
- F4: cap hit at size 60 (<= second-largest 200): 10 of 10 runs
- F4: cap hit at size 80 (<= second-largest 200): 3 of 3 runs
- F4: cap hit at size 100 (<= second-largest 200): 3 of 3 runs
- F4: cap hit at size 150 (<= second-largest 200): 3 of 3 runs
- F4: cap hit at size 200 (<= second-largest 200): 3 of 3 runs
- F5: cap hit at size 10 (<= second-largest 25): 1 of 1 runs
- F5: cap hit at size 12 (<= second-largest 25): 1 of 1 runs
- F5: cap hit at size 16 (<= second-largest 25): 1 of 1 runs
- F5: cap hit at size 20 (<= second-largest 25): 1 of 1 runs
- F5: cap hit at size 25 (<= second-largest 25): 1 of 1 runs
- F8: cap hit at size 12 (<= second-largest 14): 1 of 1 runs
- F8: cap hit at size 14 (<= second-largest 14): 1 of 1 runs
- F8: local exponent > 8 at two consecutive sizes (8, 10): e = 10.33, 11.40

### K3 (scaling fits, SDCL*, families with >= 5 fully solved sizes)

| family | fully solved sizes | poly fit: exponent, RSS | exp fit: rate, RSS | smaller RSS | fired |
|---|---|---|---|---|---|
| F1 | 4 (50, 75, 100, 200) | - | - | - | not applicable |
| F2 | 4 (100, 150, 200, 250) | - | - | - | not applicable |
| F3 | 1 (8) | - | - | - | not applicable |
| F4 | 1 (20) | - | - | - | not applicable |
| F5 | 1 (8) | - | - | - | not applicable |
| F6 | 6 (6, 8, 10, 12, 14, 16) | 6.74, 0.233 | 0.6585, 0.219 | exp | YES |
| F7 | 0 () | - | - | - | not applicable |
| F8 | 3 (6, 8, 10) | - | - | - | not applicable |

**K3 fired: YES**

- F6: exponential model has smaller RSS (0.219 vs 0.233) and polynomial exponent 6.74 > 6

### K4 (no separation from resolution: F1 UNSAT instances at n in {200, 225, 250})

| n | #UNSAT inst. | SDCL* solved/timeouts | SDCL* median cost | plain solved/timeouts | plain median cost | ratio | fired |
|---|---|---|---|---|---|---|---|
| 200 | 3 | 3/0 | 82650 | 3/0 | 24506 | 3.37 | YES |
| 225 | 3 | 1/2 | >= 145349 | 3/0 | 38449 | >= 3.78 | YES |
| 250 | 3 | 0/3 | >= 125920 | 3/0 | 201619 | >= 0.62 | YES |

**K4 fired: YES**

- F1 n=200: SDCL* median cost 82650 vs plain 24506 (ratio 3.37 >= 0.5)
- F1 n=225: SDCL* median cost >= 145349 vs plain 38449 (ratio >= 3.78 >= 0.5)
- F1 n=250: SDCL* median cost >= 125920 vs plain 201619 (ratio >= 0.62 >= 0.5)

### K5 (budget: > 10% of instances at a size up to the second-largest listed hit the 3600 s cap, SDCL*)

| family | size | n | cap hits | fraction | fired |
|---|---|---|---|---|---|
| F1 | 225 | 3 | 2 | 67% | YES |
| F1 | 250 | 3 | 3 | 100% | no (largest size) |
| F2 | 300 | 2 | 2 | 100% | YES |
| F2 | 350 | 2 | 2 | 100% | YES |
| F2 | 400 | 4 | 4 | 100% | no (largest size) |
| F3 | 10 | 1 | 1 | 100% | YES |
| F3 | 12 | 1 | 1 | 100% | YES |
| F3 | 14 | 1 | 1 | 100% | YES |
| F3 | 16 | 1 | 1 | 100% | YES |
| F3 | 20 | 1 | 1 | 100% | YES |
| F3 | 25 | 1 | 1 | 100% | YES |
| F3 | 30 | 1 | 1 | 100% | YES |
| F3 | 40 | 1 | 1 | 100% | no (largest size) |
| F4 | 40 | 10 | 10 | 100% | YES |
| F4 | 60 | 10 | 10 | 100% | YES |
| F4 | 80 | 3 | 3 | 100% | YES |
| F4 | 100 | 3 | 3 | 100% | YES |
| F4 | 150 | 3 | 3 | 100% | YES |
| F4 | 200 | 3 | 3 | 100% | YES |
| F4 | 300 | 3 | 3 | 100% | no (largest size) |
| F5 | 10 | 1 | 1 | 100% | YES |
| F5 | 12 | 1 | 1 | 100% | YES |
| F5 | 16 | 1 | 1 | 100% | YES |
| F5 | 20 | 1 | 1 | 100% | YES |
| F5 | 25 | 1 | 1 | 100% | YES |
| F5 | 30 | 1 | 1 | 100% | no (largest size) |
| F6 | 18 | 4 | 1 | 25% | YES |
| F6 | 20 | 4 | 4 | 100% | no (largest size) |
| F7 | 0 | 5 | 3 | 60% | YES |
| F8 | 12 | 1 | 1 | 100% | YES |
| F8 | 14 | 1 | 1 | 100% | YES |
| F8 | 16 | 1 | 1 | 100% | no (largest size) |

**K5 fired: YES**

- F1 size 225: 2 of 3 runs hit the cap (67%)
- F2 size 300: 2 of 2 runs hit the cap (100%)
- F2 size 350: 2 of 2 runs hit the cap (100%)
- F3 size 10: 1 of 1 runs hit the cap (100%)
- F3 size 12: 1 of 1 runs hit the cap (100%)
- F3 size 14: 1 of 1 runs hit the cap (100%)
- F3 size 16: 1 of 1 runs hit the cap (100%)
- F3 size 20: 1 of 1 runs hit the cap (100%)
- F3 size 25: 1 of 1 runs hit the cap (100%)
- F3 size 30: 1 of 1 runs hit the cap (100%)
- F4 size 40: 10 of 10 runs hit the cap (100%)
- F4 size 60: 10 of 10 runs hit the cap (100%)
- F4 size 80: 3 of 3 runs hit the cap (100%)
- F4 size 100: 3 of 3 runs hit the cap (100%)
- F4 size 150: 3 of 3 runs hit the cap (100%)
- F4 size 200: 3 of 3 runs hit the cap (100%)
- F5 size 10: 1 of 1 runs hit the cap (100%)
- F5 size 12: 1 of 1 runs hit the cap (100%)
- F5 size 16: 1 of 1 runs hit the cap (100%)
- F5 size 20: 1 of 1 runs hit the cap (100%)
- F5 size 25: 1 of 1 runs hit the cap (100%)
- F6 size 18: 1 of 4 runs hit the cap (25%)
- F7 size 0: 3 of 5 runs hit the cap (60%)
- F8 size 12: 1 of 1 runs hit the cap (100%)
- F8 size 14: 1 of 1 runs hit the cap (100%)

### Verdict

Kill criteria fired: K2, K3, K4, K5

## 5. Verdict

**C3 (SDCL\*) is KILLED under the pre-registered rules.** Four of the five kill criteria fired; K1 (correctness) did not. Stop point:
2026-10-06 09:08 local, 536 of the 1,881 planned runs recorded (breadth-first rounds: every family × size × label × mode group has at least its
first instance, most have two; the unfiltered ablation was not reached). All numbers below are from `phase4/results/runs.jsonl`; a timed-out
run contributes its cost at the cap as a lower bound ("≥").

* **K2 (home-turf exponential signature) — fired on all four home-turf families.** The 3,600 s cap was hit by SDCL\* at every listed size from
  the second one upward: F3 `PHP_{n+1}^n` for n = 10 … 40 (cost at the cap 182k at n = 10, 300k–511k at n = 12–16, decreasing to 81k at n = 40
  because the reduct checks get slower, not because the proofs get shorter); F4 Tseitin on 3-regular graphs for n = 40 … 300 (all 10 of 10
  instances at n = 40 and 60, all 3 of 3 run at n = 80 … 300; costs 41k–85k at the cap); F5 clique-colouring for n = 10 … 30 (all 1 of 1); F8
  mutilated chessboard for s = 12, 14, 16, after a local exponent of 10.3 (s = 6→8) and 11.4 (s = 8→10), which also satisfies the
  two-consecutive-sizes clause. Only the smallest size of each family was solved. On the same instances plain CDCL solves Tseitin n = 40 and 60 in
  under a second (cost 0.8k–7.7k against SDCL\*'s ≥ 48k–78k at the cap), and the original SaDiCaL (§7) solves every PHP up to n = 40 (21k
  conflicts, 26 min), every Tseitin instance up to n = 60 and most up to n = 100, and every chessboard up to 16×16 (255 s): the short PR proofs
  exist and are findable; this search does not find them. The pre-registered predictions "F3 solved with e_k ≤ 3; F4 solved by the filtered variant
  with e_k ≤ 4" failed at the first step.
* **K5 (budget) — fired** on F3, F4, F5, F8 (100% cap hits at every size from the second upward), on F2 at n = 300 and 350 (2 of 2 each), on F1
  at n = 225 (2 of 3), on F6 at b = 18 (1 of 4) and on F7 (3 of 5).
* **K4 (no separation from resolution) — fired** at all three sizes on the F1 UNSAT instances run so far (3 per size, breadth-first): median cost
  SDCL\* / plain = 82,650 / 24,506 = 3.37 at n = 200; ≥ 145,349 / 38,449 ≥ 3.78 at n = 225 (two of three SDCL\* runs at the cap); ≥ 125,920 /
  201,619 ≥ 0.62 at n = 250 (all three at the cap). The n = 250 line is the weakest: SDCL\*'s censored lower bound is only 0.62 of the plain
  median, and plain's cost there (201k in 40 s) is larger than what SDCL\* reaches in an hour; by the pre-registered cost measure the criterion fires
  at every size, but the substantive point is the first two sizes and the time-outs, not the 0.62.
* **K3 (scaling) — fired on F6** (factoring), the only family with ≥ 5 fully solved sizes: medians over b = 6 … 16 (10 instances at b = 6, 8;
  5–6 of 10 recorded at b = 10 … 16, all solved) give polynomial exponent 6.74 (RSS 0.233) against an exponential fit with the smaller RSS 0.219;
  at b = 18 one of four runs hit the cap and at b = 20 all four did, while plain CDCL solves every F6 instance up to b = 20 (median 846k, 9 min).
  This is the "must factor" consequence of PHASE3.md 2.3.7, and it fails. The fit uses the instances recorded at the stop point, not all 10 per
  size; K3 is not needed for the verdict and is reported as computed.
* **K1 — did not fire.** 536 runs (286 SDCL\*, 250 plain; 98 at the cap): 166 SAT answers, every model accepted by the independent evaluator
  and agreeing with the CaDiCaL label; 272 UNSAT answers, every one agreeing with the construction or CaDiCaL label, 269 proofs accepted by
  dpr-trim (219 of them also by the own Python checker), the remaining 3 being plain-CDCL proofs of 8–24 million conflicts on which dpr-trim
  exceeded its own 1 h limit (checker timeouts, not rejections). No crash.

What the kill means and does not mean. It means that this specific, fixed algorithm (CDCL with VSIDS/Luby plus a filtered-positive-reduct check
before every decision with a 100-conflict inner solver, learning the negated decisions as PR clauses) does not find the short PR proofs its own
proof system admits, already on 60-variable Tseitin formulas, and that its cost is not a wall-clock artefact: the cost at the cap is 10–170 times
the plain-CDCL cost on the same instances, and the schedule-convention comparison in NOTES.md shows the pre-registered cost measure is insensitive
to the database-reduction convention. On satisfiable and random instances (F1, F2, F6, F7) SDCL\* is consistently 3–10 times more expensive than its
own plain ablation and times out from n ≈ 225 (F1), n = 300 (F2), b = 18 (F6). It does not mean that PR learning is weak as a proof system (no
PR⁻/SPR⁻ lower bounds are known; that status is unchanged), nor that a different SDCL heuristic would not do better on the home-turf families:
SaDiCaL's look-ahead decision heuristics do (§7), and even SaDiCaL times out on clique-colouring from n = 10 and on Tseitin from n = 150. By the
pre-registered no-change rule any such variant is a new candidate needing a new pre-registration; none is proposed in this session. Nothing here
bears on `sat_in_p`; the project status remains **NOT PROVED**.

## 6. Censoring and other recording notes

* Every run is in `phase4/results/runs.jsonl` (status, cost, conflicts, inner conflicts, reduct checks, PR clauses, decisions, propagations, filter
  statistics, wall-clock, verification results); solver outputs in `phase4/results/out/<family>/`; verified UNSAT proofs up to 20 MB kept in
  `phase4/results/proofs/<family>/` (larger proofs were deleted after verification to save disk; the verification result is recorded).
* Timeouts: the solver stops at its own 3,600 s limit and reports its statistics; `TIMEOUT-HARDKILL` marks the rare case where the 3,700 s hard kill fired
  (no statistics). Both count as cap hits for K2 and K5 and as censored observations for medians.
* No recorded run was omitted, edited or replaced; no parameter was changed after the first measured run. The driver was restarted three times to
  change only the execution order (section 3). The three UNSAT answers whose dpr-trim check exceeded the checker's own 1 h limit are listed under K1.

## 7. Supplementary: the original SaDiCaL on the home-turf families (not part of the kill criteria)

SaDiCaL default options, text DPR proof output (`--no-binary`), 3,600 s cap (`timeout 3600` inside WSL; the runner's own 3,720 s kill is recorded as `TIMEOUT`), two concurrent runs under WSL; proofs checked with dpr-trim. `UNKNOWN` = SaDiCaL exited without an answer line (at the cap, or earlier: `cliquecol_n12` exited after 108 s with 30,816 conflicts and no result; raw output in `phase4/results/out/`). `None` in the dpr-trim column = proof file not present when the check ran (not checked). SaDiCaL's cost is not comparable to SDCL\*'s (different search; inner conflicts not reported); the table shows that short PR proofs of these instances are findable in practice.

Reproducing these runs: the SaDiCaL source is not vendored in this repository. It was obtained from its upstream page http://fmv.jku.at/sadical
(archive `https://fmv.jku.at/sadical/sadical.zip`, SHA-256 `707efdc5a291e47100c54b4ab6c1641375fea2eca49da772f0e90543802d004c`); its `VERSION`
file reads `00n`. Unpack it to `phase4/tools/sadical/` and build with `./configure.sh && make` under WSL; `phase4/src/run_sadical.py` expects the
binary at `phase4/tools/sadical/sadical/sadical`.

| family | instance | size | SaDiCaL result | conflicts | prunes | reducts | wall (s) | dpr-trim |
|---|---|---|---|---|---|---|---|---|
| F3 | php_9_8.cnf | 8 | UNSATISFIABLE | 215 | 160 | 291 | 5.2 | VERIFIED |
| F3 | php_11_10.cnf | 10 | UNSATISFIABLE | 377 | 322 | 596 | 1.9 | VERIFIED |
| F3 | php_13_12.cnf | 12 | UNSATISFIABLE | 619 | 564 | 1057 | 5.6 | VERIFIED |
| F3 | php_15_14.cnf | 14 | UNSATISFIABLE | 957 | 902 | 1706 | 10.1 | VERIFIED |
| F3 | php_17_16.cnf | 16 | UNSATISFIABLE | 1407 | 1352 | 2575 | 14.1 | VERIFIED |
| F3 | php_21_20.cnf | 20 | UNSATISFIABLE | 2707 | 2652 | 5101 | 53.3 | VERIFIED |
| F3 | php_26_25.cnf | 25 | UNSATISFIABLE | 5247 | 5192 | 10066 | 163.4 | VERIFIED |
| F3 | php_31_30.cnf | 30 | UNSATISFIABLE | 9037 | 8982 | 17506 | 330.0 | VERIFIED |
| F3 | php_41_40.cnf | 40 | UNSATISFIABLE | 21367 | 21312 | 41811 | 1565.6 | VERIFIED |
| F4 | tseitin_n20_s0.cnf | 20 | UNSATISFIABLE | 231 | 82 | 257 | 2.6 | VERIFIED |
| F4 | tseitin_n20_s1.cnf | 20 | UNSATISFIABLE | 328 | 63 | 189 | 2.0 | VERIFIED |
| F4 | tseitin_n20_s2.cnf | 20 | UNSATISFIABLE | 231 | 54 | 163 | 2.5 | VERIFIED |
| F4 | tseitin_n20_s3.cnf | 20 | UNSATISFIABLE | 410 | 78 | 221 | 2.7 | VERIFIED |
| F4 | tseitin_n20_s4.cnf | 20 | UNSATISFIABLE | 1082 | 116 | 311 | 2.7 | VERIFIED |
| F4 | tseitin_n20_s5.cnf | 20 | UNSATISFIABLE | 845 | 114 | 342 | 2.7 | VERIFIED |
| F4 | tseitin_n20_s6.cnf | 20 | UNSATISFIABLE | 778 | 82 | 247 | 2.5 | VERIFIED |
| F4 | tseitin_n20_s7.cnf | 20 | UNSATISFIABLE | 1296 | 130 | 391 | 2.8 | VERIFIED |
| F4 | tseitin_n20_s8.cnf | 20 | UNSATISFIABLE | 2538 | 133 | 480 | 2.8 | VERIFIED |
| F4 | tseitin_n20_s9.cnf | 20 | UNSATISFIABLE | 182 | 51 | 139 | 2.6 | VERIFIED |
| F4 | tseitin_n40_s0.cnf | 40 | UNSATISFIABLE | 1061 | 336 | 967 | 3.3 | VERIFIED |
| F4 | tseitin_n40_s1.cnf | 40 | UNSATISFIABLE | 3034 | 740 | 1833 | 4.9 | VERIFIED |
| F4 | tseitin_n40_s2.cnf | 40 | UNSATISFIABLE | 808 | 254 | 778 | 3.1 | VERIFIED |
| F4 | tseitin_n40_s3.cnf | 40 | UNSATISFIABLE | 10345 | 905 | 3012 | 6.1 | VERIFIED |
| F4 | tseitin_n40_s4.cnf | 40 | UNSATISFIABLE | 5966 | 603 | 1933 | 4.3 | VERIFIED |
| F4 | tseitin_n40_s5.cnf | 40 | UNSATISFIABLE | 2261 | 770 | 1862 | 5.2 | VERIFIED |
| F4 | tseitin_n40_s6.cnf | 40 | UNSATISFIABLE | 1370 | 335 | 952 | 2.7 | VERIFIED |
| F4 | tseitin_n40_s7.cnf | 40 | UNSATISFIABLE | 7248 | 768 | 2243 | 5.3 | VERIFIED |
| F4 | tseitin_n40_s8.cnf | 40 | UNSATISFIABLE | 3269 | 350 | 1104 | 3.4 | VERIFIED |
| F4 | tseitin_n40_s9.cnf | 40 | UNSATISFIABLE | 2749 | 611 | 1655 | 4.3 | VERIFIED |
| F4 | tseitin_n60_s0.cnf | 60 | UNSATISFIABLE | 19494 | 2936 | 6716 | 14.8 | VERIFIED |
| F4 | tseitin_n60_s1.cnf | 60 | UNSATISFIABLE | 4931 | 1244 | 3135 | 9.0 | VERIFIED |
| F4 | tseitin_n60_s2.cnf | 60 | UNSATISFIABLE | 1910 | 643 | 2063 | 4.4 | VERIFIED |
| F4 | tseitin_n60_s3.cnf | 60 | UNSATISFIABLE | 4138 | 1088 | 2858 | 6.7 | VERIFIED |
| F4 | tseitin_n60_s4.cnf | 60 | UNSATISFIABLE | 20955 | 14017 | 28695 | 188.3 | VERIFIED |
| F4 | tseitin_n60_s5.cnf | 60 | UNSATISFIABLE | 8230 | 2377 | 5417 | 19.1 | VERIFIED |
| F4 | tseitin_n60_s6.cnf | 60 | UNSATISFIABLE | 2176 | 876 | 2431 | 5.6 | VERIFIED |
| F4 | tseitin_n60_s7.cnf | 60 | UNSATISFIABLE | 5809 | 2556 | 5740 | 12.7 | VERIFIED |
| F4 | tseitin_n60_s8.cnf | 60 | UNSATISFIABLE | 15781 | 5102 | 11919 | 57.3 | VERIFIED |
| F4 | tseitin_n60_s9.cnf | 60 | UNSATISFIABLE | 11604 | 2296 | 5392 | 15.2 | VERIFIED |
| F4 | tseitin_n80_s0.cnf | 80 | UNSATISFIABLE | 5556 | 2498 | 5923 | 13.9 | VERIFIED |
| F4 | tseitin_n80_s1.cnf | 80 | UNSATISFIABLE | 6593 | 3439 | 7748 | 17.7 | VERIFIED |
| F4 | tseitin_n80_s2.cnf | 80 | UNSATISFIABLE | 143441 | 7441 | 32526 | 68.1 | VERIFIED |
| F4 | tseitin_n80_s3.cnf | 80 | UNSATISFIABLE | 27100 | 11861 | 26862 | 116.0 | VERIFIED |
| F4 | tseitin_n80_s4.cnf | 80 | TIMEOUT (3600 s cap) | 62226 | 60247 | 121724 | 3606.6 | - |
| F4 | tseitin_n80_s5.cnf | 80 | UNSATISFIABLE | 16326 | 10526 | 21931 | 92.6 | VERIFIED |
| F4 | tseitin_n80_s6.cnf | 80 | UNSATISFIABLE | 10871 | 5921 | 12985 | 36.8 | VERIFIED |
| F4 | tseitin_n80_s7.cnf | 80 | UNSATISFIABLE | 82515 | 71142 | 143997 | 3155.6 | VERIFIED |
| F4 | tseitin_n80_s8.cnf | 80 | UNSATISFIABLE | 11423 | 5710 | 12569 | 35.2 | VERIFIED |
| F4 | tseitin_n80_s9.cnf | 80 | UNSATISFIABLE | 27883 | 18339 | 38090 | 305.6 | VERIFIED |
| F4 | tseitin_n100_s0.cnf | 100 | UNSATISFIABLE | 50706 | 15840 | 35995 | 252.0 | VERIFIED |
| F4 | tseitin_n100_s1.cnf | 100 | UNSATISFIABLE | 543054 | 23828 | 95709 | 316.2 | VERIFIED |
| F4 | tseitin_n100_s2.cnf | 100 | UNSATISFIABLE | 101892 | 21093 | 47833 | 807.7 | VERIFIED |
| F4 | tseitin_n100_s3.cnf | 100 | UNSATISFIABLE | 20830 | 10056 | 21619 | 311.3 | VERIFIED |
| F4 | tseitin_n100_s4.cnf | 100 | UNSATISFIABLE | 35911 | 11782 | 27769 | 378.6 | VERIFIED |
| F4 | tseitin_n100_s5.cnf | 100 | UNSATISFIABLE | 49457 | 10231 | 22147 | 250.6 | VERIFIED |
| F4 | tseitin_n100_s6.cnf | 100 | UNSATISFIABLE | 24763 | 16551 | 34716 | 547.5 | VERIFIED |
| F4 | tseitin_n100_s7.cnf | 100 | TIMEOUT (3600 s cap) | 52619 | 51416 | 108103 | 3659.5 | - |
| F4 | tseitin_n100_s8.cnf | 100 | TIMEOUT (3600 s cap) | 45040 | 44073 | 88292 | 3668.7 | - |
| F4 | tseitin_n100_s9.cnf | 100 | TIMEOUT (3600 s cap) | 56263 | 54932 | 110108 | 3697.4 | - |
| F4 | tseitin_n150_s0.cnf | 150 | TIMEOUT (3600 s cap) | 44164 | 44088 | 135393 | 3699.4 | - |
| F4 | tseitin_n150_s1.cnf | 150 | TIMEOUT | None | None | None | 3723.4 | - |
| F4 | tseitin_n150_s2.cnf | 150 | TIMEOUT | None | None | None | 3721.9 | - |
| F4 | tseitin_n150_s3.cnf | 150 | TIMEOUT | None | None | None | 3721.8 | - |
| F4 | tseitin_n150_s4.cnf | 150 | TIMEOUT | None | None | None | 3721.5 | - |
| F5 | cliquecol_n8_k3_c2.cnf | 8 | UNSATISFIABLE | 65966 | 711 | 3600 | 85.8 | VERIFIED |
| F5 | cliquecol_n10_k4_c3.cnf | 10 | TIMEOUT | None | None | None | 3722.9 | - |
| F5 | cliquecol_n12_k4_c3.cnf | 12 | UNKNOWN | 30816 | 1754 | 55295 | 107.8 | - |
| F5 | cliquecol_n16_k4_c3.cnf | 16 | TIMEOUT | None | None | None | 3723.6 | - |
| F5 | cliquecol_n20_k5_c4.cnf | 20 | TIMEOUT | None | None | None | 3723.3 | - |
| F5 | cliquecol_n25_k5_c4.cnf | 25 | TIMEOUT | None | None | None | 3723.0 | - |
| F5 | cliquecol_n30_k6_c5.cnf | 30 | TIMEOUT | None | None | None | 3723.9 | - |
| F8 | mchess_6.cnf | 6 | UNSATISFIABLE | 533 | 22 | 49 | 70.5 | VERIFIED |
| F8 | mchess_8.cnf | 8 | UNSATISFIABLE | 2426 | 98 | 415 | 4.9 | VERIFIED |
| F8 | mchess_10.cnf | 10 | UNSATISFIABLE | 19928 | 422 | 2119 | 4.6 | VERIFIED |
| F8 | mchess_12.cnf | 12 | UNSATISFIABLE | 39848 | 983 | 5138 | 17.6 | - |
| F8 | mchess_14.cnf | 14 | UNSATISFIABLE | 279631 | 2487 | 15653 | 61.2 | - |
| F8 | mchess_16.cnf | 16 | UNSATISFIABLE | 1008742 | 5787 | 39311 | 254.6 | VERIFIED |
