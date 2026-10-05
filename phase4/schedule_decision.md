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
