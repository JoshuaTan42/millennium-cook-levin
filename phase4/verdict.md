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
