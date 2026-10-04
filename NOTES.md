# NOTES.md — P vs NP project log

Status: **NOT PROVED**.

## Lemma table

| Name | File | Statement (short) | Status | Evidence |
|---|---|---|---|---|
| `PvsNP.comp` | Comp.lean | `Millennium.ClayPVersusNP.Support.PolynomialTimeComputableComposition` | **proved** (2026-09-25) | `#print axioms PvsNP.comp` → `[propext, Classical.choice, Quot.sound]` |
| `PvsNP.tm2ComputableInPolyTime_comp` | Comp.lean | exact signature of Mathlib's `proof_wanted TM2ComputableInPolyTime.comp` (checked by an `example` restating it) | **proved** (2026-09-25) | `#print axioms` → `[propext, Classical.choice, Quot.sound]` |
| (side result) P ⊆ NP, unconditional | scratch check | `of_turing_machine_composition PvsNP.comp` | proved | `#print axioms` → `[propext, Classical.choice, Quot.sound]` |
| `PvsNP.SAT` (definition) | CookLevin.lean | dense CNF-SAT over `List Bool` (see "SAT: concrete definition") | **defined** (2026-09-26), no `sorry` | sanity: `decodeCNF_encodeCNF` (`#print axioms` → `[propext]`); `example`s: `¬SAT 00`, `¬SAT (x₀∧¬x₀)`, `SAT (x₀∧(¬x₀∨x₁))` |
| `PvsNP.SATDef.check_iff` | CookLevin.lean | `check w y = true ↔ cnfSat (decodeCNF w) y` | **proved** (2026-09-26) | `#print axioms` → `[propext, Classical.choice, Quot.sound]` |
| `PvsNP.SATDef.sat_iff_check` | CookLevin.lean | `SAT w ↔ ∃ y, y.length ≤ w.length ^ 1 ∧ check w y = true` | **proved** (2026-09-26) | `#print axioms` → `[propext, Classical.choice, Quot.sound]` |
| `PvsNP.Verifier.verifier` | CookLevin.lean | `TM2ComputableInPolyTime (pair_encoding …).encode finEncodingBoolBool.encode (fun p => check p.1 p.2)`, time `2(n+5)²` | **proved** (2026-09-26) | `#print axioms` → `[propext, Classical.choice, Quot.sound]` |
| **`PvsNP.sat_in_np`** (SAT ∈ NP) | CookLevin.lean | `InNondeterministicPolynomialTime (fin_encoding_string Bool) SAT` | **proved** (2026-09-26) | `#print axioms PvsNP.sat_in_np` → `[propext, Classical.choice, Quot.sound]` |
| **`PvsNP.cook_levin`** (NP-hardness + membership) | **Pkg.lean** (moved 2026-10-05 from CookLevin.lean: the reduction chain imports CookLevin, so the proof cannot live there; statement text and `pp.all` type unchanged, see "CLOSE cook_levin") | `NondeterministicPolynomialTimeComplete (fin_encoding_string Bool) SAT` | **proved** (2026-10-05): `⟨sat_in_np, CL.sat_np_hard⟩` | `#print axioms PvsNP.cook_levin` → `[propext, Classical.choice, Quot.sound]`; no `sorryAx` in its dependency closure (closure scan) |
| **`PvsNP.CL.sat_np_hard`**, **`CL.v_correct`** (item 5), `CL.v_run`, `CL.v_input`, `CL.v_time`, **`CL.encX`** / `CL.encX_acc` / `CL.symSetX` (item 6 replacement), **`CL.eval_le_pow`**, `CL.eval_mono'`, `CL.pow_weaken`, `CL.pull`; defs `vacc`, `vE`, `vr`, `veqv`, `vι`, `vsep`, `vY`, `vYs`, `vc`, `ve` (items 1–2) | Pkg.lean (root), sections [POLY]…[HARD] | `sat_np_hard`: every `L'` in NP (any `FinEncoding`) is `PolynomialTimeReducible` to `SAT` via `gComp` on the verifier's machine. `v_correct`: `L' a ↔ SAT (fR a)`. `encX`: `Enc.ofFinTM2` with the accept symbol added to the effective output alphabet, so `hacc` holds unconditionally. `eval_le_pow`: every `p : Polynomial ℕ` has `c ≥ 1`, `e` with `p.eval j ≤ (j + c)^e` | **proved** (2026-10-05) | `#print axioms` of `sat_np_hard`, `v_correct`, `encX_acc` → `[propext, Classical.choice, Quot.sound]` |
| D1 library `PvsNP.Prog.*` (Run/sequencing, counters, `incr`/`decr`, `xfer`, `cmp`, `forLoop`, `emit`, `sumFrom_le`; **extended** with `copy_run`/`add_run`/`mul_run`, `xferE_run`, `emitDiff_run`, `Reach`, `forLoop_reach`; **2026-09-28:** `RunLe`, `Bud` chaining, `forLoop_le`) | Prog.lean (**lakefile root since the third 2026-09-27 session**) | generic TM2 program primitives with exact step counts (see "D1 LIBRARY") | **proved** (2026-09-27), no `sorry`, banned-token scan clean | `#print axioms` of every declaration within `[propext, Classical.choice, Quot.sound]` (full list in the D1 section) |
| `PvsNP.D3Fam.gen_time` / `gen_run` / `gen_correct` (EXPLORATORY) | D3Fam.lean (**lakefile root since 2026-09-28**, still exploratory) | the parametric generator, now with **finite labels** (`GL N nLits`, `Fin`-indexed; `genTM : FinTM2` typechecks) and an **explicit time bound**: halts within `genBound L N T H ≤ genC L N · (T+H+1)^5` steps with `encodeCNF` of the family | **proved** (2026-09-28) | `#print axioms` of all 95 D3Fam declarations ⊆ `[propext, Classical.choice, Quot.sound]`, no `sorryAx`; see "FINITE LABELS + TIME BOUND" |
| `PvsNP.D3OH.oh_time` / `oh_run` (EXPLORATORY, 2nd family: cell one-hot, **runtime inner loops**) | D3OneHot.lean (**lakefile root since 2026-09-29**, still exploratory; imports D3Fam) | generator for the P2 cell one-hot family (at-least-one + pairwise at-most-one per cell, all `t ≤ T`, `k < KK`, `j < H`); three nested runtime loops; finite labels `GL g`; `ohTM : FinTM2` typechecks; halts at `done` within `ohC L·(T+H+1)^6` steps with `encodeCNF (ohFamily L T H)` prepended; no hypotheses | **proved** (2026-09-28) | `#print axioms` of all 92 D3OneHot declarations ⊆ `[propext, Classical.choice, Quot.sound]`, no `sorryAx`; see "INNER-LOOP FAMILY" |
| `PvsNP.D3SH.sh_time` / `sh_run` / `pf_run` / `depth_cover` (EXPLORATORY, 3rd family: **cell shifts + overflow + pushed fill**, the complete cell part of the transition constraint) | D3Shift.lean (**lakefile root since 2026-09-29, second session**; imports D3OneHot) | `S[t,i]` at `xIdx H (t+1) (sa i)`. Per `t < T, i < N, k < KK`: in-range `¬C[t,k,u+c,x] ∨ ¬S[t,i] ∨ C[t+1,k,u+p,x]` (`u < H − max p c`, `x < g`); overflow `¬S[t,i] ∨ C[t+1,k,H−c+p+r,⊥]` (`r < c − p`); **pushed fill `¬S[t,i] ∨ C[t+1,k,j,pu i k j]` (`j < p`, added 2026-09-29 second session; new table `pu`, clause kind `CL.pf (j : Fin d)`)**. Runtime `t`/`u`/`r` loops, label chains `i`/`k`/`x`/`j`; finite labels; `shTM : FinTM2` typechecks; halts at `done` within `shC L N·(T+H+1)^6` steps (`shC` constant 616 → 828) with `encodeCNF (shFamily …)` prepended; hypothesis `WF` only (codes in range incl. `pu i k j < g`, `p, c ≤ d ≤ H`, `0 < g`). `depth_cover`/`depth_disjoint`: the three regions cover every depth `j < H` and are disjoint | **proved** (2026-09-28; re-targeted and extended 2026-09-29) | `#print axioms` of all 108 D3Shift declarations ⊆ `[propext, Classical.choice, Quot.sound]`, no `sorryAx`; `lake build` checks it; see "CELL-SHIFT FAMILY", "SITUATION VARIABLES", "PUSHED FILL" |
| `PvsNP.D3SD.sd_time` / `sdFamily_eq` / `sdLits_eq` / `sd_sorted` (EXPLORATORY, 4th family: **situation definitions** `¬X[t,la i] ∨ ⋁¬C[t,k,j,wa i k j] ∨ S[t,i]`) | D3SDef.lean (not a root; imports D3Shift; checked with `lake env lean`) | family stated independently (`sIdx`, `winLits`, `sdLits`, `sdFamily`); **proved equal to `D3Fam.family L la sa wa`** (D3Fam with `na := sa`); hence generator `sdTM : FinTM2` (finite labels) halts at `done` within `genC L N·(T+H+1)^5` steps with `encodeCNF (sdFamily …)` prepended; `shLits_S`/`ovLits_S`/`pfLits_S` (last added 2026-09-29, second): D3Shift's `S` literal is `sIdx` in all three clause kinds; `sIdx_block`: `S` lies in row `t+1`'s `A` block | **proved** (2026-09-29) | `#print axioms` of all 14 D3SDef declarations ⊆ `[propext, Classical.choice, Quot.sound]`, no `sorryAx`; see "SITUATION VARIABLES" |
| `PvsNP.Sit.Enc.{wf_upd,wf_sdef,wf_sh,pu_valid,halted,sit_surj}`, `Enc.ofFinTM2`, `upd_time`/`sdef_time`/`shift_time` (EXPLORATORY, **B2+B3: situation tables of an arbitrary real `FinTM2`**) | Sit.lean (**lakefile root since 2026-09-30**; imports D3Shift) | for any `M : FinTM2` and encoding record `E : Enc M` (a classical one exists for every `M`: `Enc.ofFinTM2`), tables `la wa sa na pl cn pu` with the step on `Option Λ` (`none` idles); all three proved generators accept them (`depth M ≤ H` only); `pu` codes are valid per stack and decode to the real pushed symbol; halted situations keep their code with `p = c = 0`; every (code, windows) is some `i < N`; kernel-checked 10-step run of a toy machine that halts at step 7 matches the table-driven update row by row | **proved** (2026-09-29, third) | `#print axioms` of all 75 declarations ⊆ `[propext, Classical.choice, Quot.sound]`, no `sorryAx`; see "B3: SITUATION TABLES" |
| `PvsNP.Sit.eff_agree`, **`step_agree`** (B1), **`Enc.table_agree`** / `Enc.table_agree_run` (B1-T), `Enc.run_good` (B2 `run_mem_Γfin`) | Sit.lean (root) | **B1:** for every `M : FinTM2` and every `c : M.Cfg`, `stepI M c = applyEff c.stk (sitStep M c.l c.var (winC M c))`: full `TM2.Cfg` equality with the idle-extended real step, with **no hypotheses**. **B1-T:** for `E : Enc M`, `Good c` and all heights `≤ H − depth M`: `sitIdx c < N`, `la = code c`, windows match, `code (stepI c) = na (sitIdx c)`, and all `KK·H` cells of the next row `= tabRow` (pushed fill / in-range shift / overflow ⊥). On real runs `Good` is discharged (`run_good`), leaving the height hypothesis only. Second machine `ex2M` (3 stacks, `d = 6`) kernel-checked for 14 rows (evidence) | **proved** (2026-09-30) | `#print axioms` of all 44 new declarations ⊆ `[propext, Classical.choice, Quot.sound]`, no `sorryAx`; `step_agree`/`eff_agree` → `[propext, Quot.sound]`; see "B1: AGREEMENT THEOREM" |
| `PvsNP.Sit.sh_force` (C6-L1), `Enc.sh_hold` / `Enc.sh_step_cell` / **`Enc.sh_step_run`** / `Enc.sh_step_run_pos` (C6-L2/L3), `clauseSat_dense` (L0), defs `Tr`, `Enc.CellsAre`, `Enc.CellsHold` | Sit.lean (root), section `[C6]` | **First clause semantics on an assignment `a : List Bool`.** L1: `cnfSat (shFamily …) a`, `S[t,i]` and `C[t,k,u+c,x]` true ⇒ `C[t+1,k,u+p,x]` true (in-range kind only). L3: if row `t` is exactly the one-hot image of `cell (runI t)` and `S[t, sitIdx]` is true, with at-most-one at the target, then every in-range cell of row `t+1` is exactly `cell (runI (t+1))`, **with no row decoding**. L3⁺: the same for the positive invariant, with no one-hot hypothesis. Hypotheses still open: `S` true (S-def family), at-most-one (one-hot family), heights `≤ H − depth M` | **proved** (2026-09-30, third) | `#print axioms` of all 10 new declarations ⊆ `[propext, Classical.choice, Quot.sound]`, no `sorryAx`; see "C6, FIRST CLAUSE-FORCING LEMMA" |
| `PvsNP.Sit.capH`, `runI_height`, `initList_height`, **`capH_height`**, `depth_le_capH`, `capH_c1`, `capH_c2` (corrected stack cap; A5) and `region_cover`, **`Enc.cells_step_run`** (depth_cover assembly), **`Enc.row_step_run`**, `Enc.row_step_capH` (one-step invariant) | Sit.lean (root), end of section `[C6]` | `capH m T d = m + (T+1)·d + 1` (P2, fix A). `capH_height`: `|s| ≤ m`, `t ≤ T` ⇒ all heights of `runI (initList s) t` are `≤ capH − depth M`. `region_cover`: every `j < H` is in exactly one of `j < pl`, `[pl, H − max pl cn + pl)`, `[H − max pl cn + pl, H)` (no hypotheses). `cells_step_run`: S-def + shift families satisfied, `hh`, `depth M ≤ H`, positive row-`t` invariant ⇒ `CellsHold` at row `t+1` for all `k < KK`, `j < H`. `row_step_run`: plus update family ⇒ `CodeHolds ∧ CellsHold` at row `t+1`. `row_step_capH`: same at `H = capH`, only `|s| ≤ m` left. **No `2d ≤ H` hypothesis.** | **proved** (2026-09-30, sixth) | `#print axioms` of all 10 ⊆ `[propext, Classical.choice, Quot.sound]` (`depth_le_capH`, `capH_c1`, `capH_c2`, `initList_height` → `[propext, Quot.sound]`), no `sorryAx`; see "H CORRECTION + DEPTH_COVER ASSEMBLY" |
| `PvsNP.Sit.Enc.rows_run` (row-`t` induction), `Enc.rows_capH`, `Enc.rows_of_init`; def `Enc.Row0` | Sit.lean (root), section `[C6]` | `rows_run`: update + S-def + shift families satisfied, heights `≤ H − depth M` on rows `t < T`, `depth M ≤ H`, and `Row0 a H s` ⇒ `∀ t ≤ T, CodeHolds ∧ CellsHold` for `runI M (initList M s) t` (POSITIVE only). `rows_capH`: same at `H = capH`, only `|s| ≤ m` + `Row0` left (both **unchanged** 2026-10-01, verified by hash). `rows_of_init` (**restated 2026-10-01**): `InitObl a x Ys m T` ⇒ ∃ `y ∈ Ys*`, `|x ++ y| ≤ m`, full-run invariant for `initList M (x ++ y)`. | **proved** (2026-09-30, seventh; `rows_of_init` restated 2026-10-01) | `#print axioms` → `[propext, Classical.choice, Quot.sound]`; `Row0` → `[propext, Quot.sound]`; no `sorryAx` |
| **`PvsNP.Sit.Enc.initFamily`** (I1–I6: `initCode`, `initOther`, `initIn`, `initCert`, `initPre`, `initTail`), def **`Enc.InitObl` (strengthened: input pinned)**, **`Enc.init_row0`**, **`Enc.init_obl`**, **`Enc.rows_of_initFamily`**, helpers `cnfSat_append`, `unit_force`, `zIdx`, `initList_k₀`, `initList_ne` | Sit.lean (root), end of `[C6]` | Row-0 clauses for fixed input prefix `x`, certificate alphabet `Ys`, bound `m`: start code; other stacks ⊥; `x` pinned; certificate cells ⊥ or `Ys`; prefix form; ⊥ from depth `m`. `InitObl a x Ys m T := ∃ y, (∀ z ∈ y, z ∈ Ys) ∧ |x ++ y| ≤ m ∧ Row0 a capH (x ++ y)`. `init_row0`: `|x| ≤ m < H`, `cnfSat initFamily` ⇒ that at general `H`; `init_obl`: at `capH`. `rows_of_initFamily`: transition + init families ⇒ ∃ `y ∈ Ys*` whose real run on `x ++ y` is tracked for all `t ≤ T`. **No placeholder left; conditional only on clause satisfaction. Non-vacuity (C5) and accept (needs at-most-one) open. Generator (D) for init unbuilt.** | **proved** (2026-10-01) | `#print axioms`: `init_row0`, `init_obl`, `rows_of_initFamily`, `unit_force` → `[propext, Classical.choice, Quot.sound]`; defs, `cnfSat_append`, `initList_k₀/ne` → `[propext, Quot.sound]`; no `sorryAx`; see "INIT FAMILY + STRENGTHENED `InitObl`" |
| **`PvsNP.Sit.Faithful` / `FamOK` / `FamPos`, `clauseSat_iff`**, `faithful_of_inc`/`_of_pol`/`_pos`/`_single`, `fam_pos`, `sh_pos`, **`Enc.upd_pos`, `Enc.sdef_pos`, `Enc.shift_pos`, `Enc.init_pos`, `Enc.acc_ok`** | Sit.lean (root), end of `[C6]` | **No literal of any family is dropped** (out of range or shadowed): every clause of update/S-def/shift (`depth M ≤ H`), init (`|x| ≤ m < H`) and accept (`0 < H`) is `denseClause V ls` with `Faithful V ls`; exact semantics `clauseSat (denseClause V ls) a ↔ ∃ (p,b) ∈ ls, a[p]? = some b` | **proved** (2026-10-01, second) | `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`; defs → none; no `sorryAx` |
| **`PvsNP.Sit.Enc.accFamily`** (`accCode`, `accCell`, `acode`), `Enc.acc_code`, `Enc.acc_cell`, def `Accepts`, **`Enc.accept_sound`**, **`Enc.unsat_of_noAccept`**, **`Enc.trans_allTrue`**, **`Enc.accFamily_allTrue`**, `Enc.A0_two`; link `runI_haltList`, `accepts_haltList`, `runI_halted`, `runI_add`, `runI_of_iterate` | Sit.lean (root), end of `[C6]` | accept = row-`T` code block exactly `lc(none, v₀)` and top of `k₁` exactly `enc acc` (positive unit + negated units = at-least-one + at-most-one). `accept_sound`: update+S-def+shift+init+accept satisfied at `capH`, `|x| ≤ m`, `acc ∈ dec k₁` ⇒ ∃ `y ∈ Ys*`, `|x++y| ≤ m`, real run on `x++y` halted with `acc` on top of `k₁` at row `T`; **no other at-most-one used**. All-true satisfies the four earlier families, fails accept. `runI_haltList`: `TM2OutputsInTime` within `p ≤ T` ⇒ `runI … T = haltList`. **Completeness (C5) not proved.** | **proved** (2026-10-01, second) | `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorryAx` |
| `PvsNP.D3Acc.acc_run` / **`acc_time`** / **`acc_gen_time`** / `accFamily_eq` (EXPLORATORY, accept generator) | D3Acc.lean (**lakefile root since 2026-10-01, third**; imports `Sit`) | `accTM : FinTM2` (finite labels) emits `encodeCNF (E.accFamily acc T H)` (`accFamily_eq` by `rfl`) within `accC·(T+H+1)^4` steps, `accC = 314·(A+KK+g+A0+kc k₁+1)^5`; only `0 < H` assumed | **proved** (2026-10-01, second) | `#print axioms` of all 44 D3Acc declarations ⊆ `[propext, Classical.choice, Quot.sound]`, no `sorryAx` |
| **`PvsNP.Sit.Enc.accept_complete`** (C5), **`Enc.five_iff`**, `Enc.init_complete`, `Enc.acc_complete`, `Enc.shift_complete`, `Enc.upd_complete`, `Enc.sdef_complete`, `Enc.fam_complete`; def **`Enc.RunLit`**, **`Enc.runAsg`** (+ `runAsg_length`, `runAsg_get`, `sat_run`, `sat_unit`); readback `Enc.lit_x`/`lit_c`/`lit_s`, `Enc.sa_lt`, `Enc.code_lt`, `Enc.lit_cell0`, `Enc.cell0_k₀`; **situation injectivity `Enc.sit_inj`** (+ `mod_pow_eq_of_digits`); **index inversion** `row_pos_inj`, `cIdx_split`, `cell_off_lt`, `A_le_rowW`, `xIdx_inj`, `xIdx_ne_cIdx`, `cIdx_inj` | Sit.lean (root), end of `[C6]` (block `[C5]`) | `runAsg s T H` = exact one-hot image of the real run on `s` over `numVars T H` variables (code, all `KK·H` cells, `S[t, sitIdx(row t)]` in row `t+1`, row-0 situation block false). `accept_complete`: `y ∈ Ys*`, `|x++y| ≤ m`, `Accepts (runI … (x++y)) T acc` ⇒ `runAsg (x++y) T capH` has length `numVars` and satisfies update, S-def, shift, init, accept (no `|x| ≤ m`, no `hacc`). `five_iff`: with `|x| ≤ m`, `hacc`: (∃ a satisfying the five families) ⟺ (∃ y ∈ Ys*, `|x++y| ≤ m`, run accepts at row `T`). | **proved** (2026-10-01, third) | `#print axioms` (ScratchC5Ax.lean, all 30 new decls) ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorryAx`; `RunLit`, `lit_cell0`, `cell0_k₀`, index-inversion lemmas → `[propext, Quot.sound]` (`cIdx_split` → `[propext]`) |
| `PvsNP.D3Init.init_run` / **`init_time`** / **`init_gen_time`** / **`init_gen_capH`** / **`initFamily_eq`** / `denseClause_congr`; primitive **`run_lift`** / `runLe_lift` / `stepAux_liftS` / **`read_run`** (EXPLORATORY, init generator, the last D-block generator) | D3Init.lean (**lakefile root since 2026-10-02**; imports `Sit`) | `initTM : FinTM2` (finite labels; stacks = D3OneHot counters + one input stack over `Fin g` holding the codes of `x`, reversed) emits `encodeCNF (E.initFamily x Ys m T H)` within `initC·(T+H+1)^5` steps, `initC = 18928·(A+KK+g+|ycs|+kc k₀+1)^5`. Inputs: unary `T`, `|x|`, `m−|x|`, `H−m`; only `|x| ≤ m < H` assumed (`init_gen_capH`: only `|x| ≤ m`, at `H = capH`). `initFamily_eq`: Sit's I1–I6 = the generator's family with I4 **sorted and deduplicated** (CNF equality) | **proved** (2026-10-01, fourth) | `#print axioms` of all 122 D3Init declarations ⊆ `[propext, Classical.choice, Quot.sound]` (43 use no axioms), no `sorryAx` |
| **`PvsNP.Emb.run_embed`** / `runLe_embed` / `stepAux_mapS`; defs `SEmb`, `mapS`, `Embeds`, `Agree`, `Frame` (generalized `run_lift`: stack/label embedding) | Emb.lean (**lakefile root since 2026-10-03**; imports only `Prog`) | For an injective stack renaming `e` with per-stack alphabet bijections `ι k : Γ k ≃ Γ' (e k)` and any label map `φ`, if the host runs `mapS (M l)` at `φ l` (except where `M` halts), a run of `M` of length `n` ending at a live label is a run of the host of length `n` from any host stacks agreeing with `M`'s on the image of `e`; at the end the host agrees again and is unchanged outside the image | **proved** (2026-10-02) | `#print axioms` of all 13 Emb declarations ⊆ `[propext, Quot.sound]`; `run_embed` → `[propext, Quot.sound]` |
| **`PvsNP.Asm.seq_run`**, **`Asm.real_run`**, **`Asm.phi_iff`**, `Asm.run_lift'` (sanity: `run_lift` re-derived from `run_embed`); defs `HK`/`HΓ` (host stacks: shared `out`, `inp`, private counter blocks `up`/`sd`/`sh`/`ac`/`ini`), `embU/S/H/A/I`, `HL`, `hprog`, `hostTM : FinTM2`, `realProg`, `Phi`, `realB` (assembly after the precomputation) | Asm.lean (**lakefile root since 2026-10-03**; imports `D3Init`, `D3Acc`, `Emb`) | `seq_run`: generic in the five sub-programs, the host runs init → update → S-def → shift → accept (1 chaining step each) from host stacks with each private block preloaded, prepending the five words. `real_run`: on the real generators of `M`, from preloaded blocks (`T`, `H = capH m T (depth M)`; init: `T, |x|, m−|x|, H−m`, reversed codes of `x` on `inp`), halts within `realB` (= sum of the five bounds + 5) with output `encodeCNF (Phi E x Ys acc m T) ++ o`; only `|x| ≤ m`. `phi_iff`: `Phi` satisfiable ⇔ accepting certificate (`five_iff` through the concatenation) | **proved** (2026-10-02) | `#print axioms` of all 37 Asm declarations ⊆ `[propext, Classical.choice, Quot.sound]` (`real_run`, `phi_iff`, `hostTM`, `realProg`, `realB` use all three), no `sorryAx` |
| **`PvsNP.Pre.full_run`**, **`Pre.full_time_poly`**, `Pre.fullB_poly`, `Pre.pre_run`, `Pre.cprog_run`, `Pre.read_run`, `Pre.pow_run`, `Pre.xferS`, `Pre.initList_full`; defs `fprog`, `fullProg`, `fullTM : FinTM2`, `cprog`, `rdT`, `IsPoly`, `mOf`, `TOf`, `fullB` (D2 precomputation, composed) | Pre.lean (**lakefile root since 2026-10-04**; imports `Asm`) | `full_run`: from the raw input `s : List (Fin r)` (= `initList fullTM s`), the full machine (one-label read loop; counter program computing `n^k`, `m = n+1+n^k`, `T = (m+c)^e`, `H = capH m T (depth M)` and loading the 12 private counters, embedded by `run_embed`; then `realProg` embedded) reaches `h fin` within `fullB |s|` steps with output `encodeCNF (Phi E (s.map ι ++ [sep]) Ys acc m T) ++ o`; **no hypotheses** (`|x| ≤ m` discharged). `full_time_poly`: one `p : Polynomial ℕ` bounds every run | **proved** (2026-10-03) | `#print axioms` of all 60 Pre declarations ⊆ `[propext, Classical.choice, Quot.sound]` (`full_run`, `full_time_poly`, `pre_run`, `cprog_run` use all three), no `sorryAx` |
| **`PvsNP.Pkg.gComp`** (`TM2ComputableInPolyTime ea (fin_encoding_string Bool).encode fR`), **`Pkg.g_run`**, **`Pkg.g_outputs`**, `Pkg.gB_poly`, `Pkg.g_run_gen`, **`Pkg.drain_run`**, `Pkg.xfer_drain`, **`Pkg.run_height`**, `Pkg.run_runI`, `Pkg.initList_g`, `Pkg.haltList_g`, `Pkg.outputsOfRunLe`; defs `gTM : FinTM2`, `gprog`, `DL`, `drainS`, `drainB`, `dks`, `phiOf`, `fR`, `gB` (block A items 3–4: halting cleanup + packaging) | Pkg.lean (**lakefile root since 2026-10-05**; imports `Pre`) | `run_height` (generic, any `FinTM2`): `Run M.m n c d` ⇒ each stack grows by `≤ n · depth M` (reuses `Sit.runI_height`). `drain_run` (generic `K, Γ, Λ, σ`): empties every stack of a `Nodup` list and halts with state `tag false` in `Σ(|S k|+1)+1` steps. `g_run`: for every raw `s`, `RunLe gTM.m (gB |s|) (initList gTM s) (haltList gTM (encodeCNF (Phi E (s.map ι ++ [sep]) Ys acc (mOf k |s|) (TOf k c e |s|))))`, **no hypotheses**. `g_outputs`: one `p : Polynomial ℕ` with `TM2OutputsInTime` for all `s`. `gComp`: the `TM2ComputableInPolyTime` structure for any `ea`, `eqv : Fin r ≃ αΓ`; still parametric in `M, E, Ys, acc, ι, sep, k, c, e` (item 2) | **proved** (2026-10-04) | `#print axioms` of all 30 Pkg declarations: 0 `sorryAx`; 22 `[propext, Classical.choice, Quot.sound]`, 4 `[propext, Quot.sound]`, 2 `[propext]`, 2 none; an `example` checks `gComp eb.encode` fits `∃ f (_ : TM2ComputableInPolyTime eb.encode (fin_encoding_string Bool).encode f), …` |
| `PvsNP.sat_in_p` | SatInP.lean | `InPolynomialTime (fin_encoding_string Bool) SAT` — **the open problem** | open (placeholder stub) | — |

`p_eq_np := ClayPVersusNP.nondeterministic_polynomial_time_complete_in_polynomial_time PvsNP.comp PvsNP.cook_levin PvsNP.sat_in_p`
(Solution.lean, which now also imports `Pkg`, builds; `#print axioms p_eq_np` → `[propext, sorryAx, Classical.choice, Quot.sound]`.
**Since 2026-10-05 the `sorryAx` comes only from `sat_in_p`**: a closure scan over every constant `p_eq_np` depends on
finds exactly one constant whose own body uses `sorryAx`, namely `PvsNP.sat_in_p`.)

Comp.lean is done: no `sorry`, banned-token scan clean. lean4checker not yet run (owed before any
READY FOR CHECK).

---

## Comp: composition of polynomial-time TM2 machines

### Target signature

Mathlib `Computability/TuringMachine/Computable.lean:284`:

```lean
proof_wanted TM2ComputableInPolyTime.comp
    {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ}
    {eγ : γ → List γΓ} {f : α → β} {g : β → γ} (h1 : TM2ComputableInPolyTime eα eβ f)
    (h2 : TM2ComputableInPolyTime eβ eγ g) :
  Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f))
```

The repo's hypothesis `ClayPVersusNP.Support.PolynomialTimeComputableComposition` is exactly this
statement specialised to `eα := ea.encode` etc. for `FinEncoding`s, with implicit arguments.
(`proof_wanted` declares nothing, so our theorem gets a fresh name, `Turing.TM2ComputableInPolyTime.comp'`
— no shadowing.)

### What Mathlib has

Nothing to build on: no untimed `TM2Computable.comp` either. `TM2to1` (TM2→TM1 simulation) and
`ToPartrec` (TM2 implementation of `Partrec` codes) exist but do not compose `FinTM2`s.

### Model facts that matter (differences from textbook two-tape composition)

1. **Stacks, not tapes.** Input list `l` sits on stack `k₀` with `l.head` on top; output on `k₁`
   with head on top. Popping from one stack and pushing onto another **reverses**, so moving
   M1's output to M2's input takes two transfers (via a scratch stack) to preserve order.
2. **Strict halting convention.** `haltList` demands label `none`, state = `initialState`, and
   **every stack other than `k₁` empty**. M1's halting config therefore has exactly its output on
   `k₁₁` and nothing else — nothing to clean up — and M2 ends in its own clean halting config.
3. **Different stack index types / alphabets.** The composite has stacks `K₁ ⊕ K₂ ⊕ {tmp}`;
   alphabets are glued via the equivalences `out₁ : Γ₁ k₁₁ ≃ βΓ`, `in₂ : Γ₂ k₀₂ ≃ βΓ`; a symbol
   is translated by `φ y := in₂.symm (out₁ y)`.
4. **Symbols in the finite control.** `push k f` needs a *total* `σ → Γ k`; `Γ₂ k₀₂` may be
   empty, so there is no default symbol. Fix: carry the popped symbol in the **label**
   (`push1 x`, `push2 x` for `x : Γ₂ k₀₂`), which is a finite type.
5. **One step = one statement tree.** Each step runs a whole `Stmt`. The lifted statement of M1's
   label is executed in one composite step, so M1-steps and composite steps correspond 1:1.
6. **Output-length bound needed.** M2's time is `p₂(|eβ(f a)|)`, but `|eβ(f a)|` is not given
   by hypothesis. Each step pushes at most `c := Σ_l pushes(m₁ l)` symbols (count `push` nodes in
   each statement tree), and M1's `k₁₁` starts with length ≤ n. So `|eβ(f a)| ≤ n + c·p₁(n)`.

### Composite machine M

* `K := K₁ ⊕ K₂ ⊕ Unit`, `Γ (inl k) = Γ₁ k`, `Γ (inr (inl k)) = Γ₂ k`, `Γ tmp = Γ₂ k₀₂`.
* `Λ := Λ₁ ⊕ Λ₂ ⊕ (Option X ⊕ Option X)` with `X = Γ₂ k₀₂`:
  `pop1 = none`, `push1 x = some x` (first copy), `pop2`, `push2 x` (second copy).
* `σ := σ₁ × σ₂ × Option X`, initial `(init₁, init₂, none)`. `k₀ := inl k₀₁`, `k₁ := inr (inl k₁₂)`.
* Program:
  - M1's label `l`: `lift₁ (m₁ l)` — acts on first state component and `inl` stacks; `halt ↦ goto pop1`.
  - `pop1`: pop `inl k₁₁`, store `φ y` in the third component; goto `push1 x` if some, else `pop2`.
  - `push1 x`: push `x` on `tmp`; goto `pop1`.
  - `pop2`: pop `tmp` into third component; goto `push2 x` if some, else M2's `main`.
  - `push2 x`: push `x` on `inr (inl k₀₂)`; goto `pop2`.
  - M2's label `l`: `lift₂ (m₂ l)`, `halt ↦ halt`.

### Run and time bound

Let `n = |eα a|`, `L` = M1's output list (`|L| = |eβ (f a)| =: m`).

1. Phase 1 simulates M1 step-for-step: `s₁ ≤ p₁(n)` steps, ends at `pop1` with `L` on `inl k₁₁`,
   all else empty, state `(init₁, init₂, none)` (M1's halting state is `init₁`).
2. Copy 1: `2m + 1` steps; `tmp = (map φ L).reverse`, `inl k₁₁ = []`.
3. Copy 2: `2m + 1` steps; `inr (inl k₀₂) = map φ L = map in₂.symm (eβ (f a))` = M2's initial input;
   third state component back to `none`. Config = embedding of `initList M2 …`.
4. Phase 2 simulates M2: `s₂ ≤ p₂(m)` steps, ends in the composite `haltList`.

Total `= s₁ + (2m+1) + (2m+1) + s₂ ≤ p₁(n) + 4(n + c·p₁(n)) + 2 + p₂(n + c·p₁(n))`, using
`m ≤ n + c·p₁(n)` and monotonicity of `Polynomial ℕ` evaluation (proved by hand; not found in
Mathlib). As a polynomial: `p₁ + C 4 · (X + C c · p₁) + C 2 + p₂.comp (X + C c · p₁)`
(`PvsNP.Comp.compTime`). So the textbook `p₂(p₁(n))` becomes `p₂(n + c·p₁(n))`, because output
length is bounded by input + pushes, not by time alone.

*Correction logged:* the first draft of this note (and of `compTime`) said `2·(X + c·p₁)`. That
undercounts the two copy loops (`4m + 2` steps total); `omega` refused the bound and exhibited the
gap, and the coefficient was fixed to 4.

### Proof architecture (Lean)

* Generic simulation lemma: if `f c = some c' → g (e c) = some (e c')`, then
  `(flip bind f)^[n] (some c) = some d → (flip bind g)^[n] (some (e c)) = some (e d)`.
  (Halted configs are absorbing, so every intermediate config is live.)
* `stepAux (lift₁ q) … = emb₁ (stepAux q …)` by induction on `q`; same for `lift₂`.
* Copy loops by induction on the list.
* Length bound by induction on `q`, then on the iteration count.

### Session log 2026-09-25

* Workspace setup: `Challenge.lean`, `Solution.lean` and the lakefile were **not** present despite
  the session brief; created `lakefile.toml` (path dependency on `LeanMillenniumPrizeProblems`,
  `packagesDir` shared with the repo so the pinned mathlib/Physlib clones are reused),
  `lean-toolchain` (v4.31.0), `Challenge.lean` verbatim from the master prompt, `Solution.lean`
  (one-line derivation), and placeholder `CookLevin.lean` / `SatInP.lean` stubs.
* Lean pitfalls hit: (1) `CΓ` must be `@[reducible]` or `simp` cannot see list types through it;
  (2) `FinTM2.Cfg` vs `TM2.Cfg` spelling blocks `rw`, use `erw`/`change`; (3) destructure
  `outputsFun` results instead of `let`-binding them (ill-typed rewrite motives).
* Next for Comp: nothing. Next overall: CookLevin.lean (not started this session, per instruction).

---

## SAT: concrete definition (session 2026-09-26, written before the proof)

### Manifest check (done first, this session)

`lakefile.toml` sets `packagesDir = "LeanMillenniumPrizeProblems/.lake/packages"`. Our
`lake-manifest.json` pins mathlib `fabf563a…` (`inputRev v4.31.0`) and Physlib `3dddd61e…`,
identical to the problems repo's own manifest (repo HEAD `603053dc…`). The checked-out clones in
that directory are at exactly those commits (`git rev-parse HEAD`), and mathlib's tag `v4.31.0`
resolves to `fabf563a…`. There is no second `packages/` directory under `D:\PvsNP\.lake`.

### Data

* **Literal slot** (`Option Bool`): `none` = variable absent from the clause, `some b` = the
  literal "x_j = b" (`some true` = x_j, `some false` = ¬x_j).
* **Clause** (`List (Option Bool)`): *dense* row; entry `j` talks about variable `x_j`.
  Clause width is arbitrary (no k-SAT restriction; empty clause allowed and unsatisfiable).
* **CNF** (`List Clause`): conjunction of the clauses; any number of clauses.
* **Assignment** (`List Bool`): `a[j]` is the value of `x_j`; variables beyond `a.length` are
  unassigned and satisfy no literal (so a short assignment is never *more* powerful).
* `clauseSat c a := ∃ j b, c[j]? = some (some b) ∧ a[j]? = some b`
* `cnfSat φ a := ∀ c ∈ φ, clauseSat c a`

### Bit encoding (`List Bool`, 2 bits per token)

| bits | token |
|---|---|
| `00` | end of clause |
| `01` | `none` (variable absent) |
| `10` | `some true` (positive literal) |
| `11` | `some false` (negative literal) |

`decodeCNF : List Bool → CNF` is **total**: each clause is the slots read up to its `00`; a
trailing unterminated clause and a dangling odd bit are ignored. `encodeCNF` is the obvious
inverse on CNFs (`decodeCNF (encodeCNF φ) = φ`, to be proved as a sanity lemma).

**Language:** `SAT w := ∃ a : List Bool, cnfSat (decodeCNF w) a`.

### Rationale / trap check

* *Not vacuous:* `00` decodes to `[[]]` (one empty clause), unsatisfiable; `10 00 11 00`
  decodes to `x₀ ∧ ¬x₀`, unsatisfiable. `10 00` (`x₀`) is satisfiable by `[true]`.
* *Not a fragment:* arbitrary widths, arbitrary numbers of clauses and variables. The dense
  encoding cannot write a clause containing both `x_j` and `¬x_j` (tautological, can be deleted)
  or a repeated literal (idempotent) — neither loses any CNF up to equivalence.
* *Polynomially faithful:* a CNF with `m` clauses over `n` variables costs `2m(n+1)` bits. A
  standard sparse encoding of size `s` has `m, n ≤ s`, so the dense one has size `≤ 2s(s+1)`:
  conversion is polynomial both ways, so NP-hardness of standard CNF-SAT transfers (needed for
  the hardness half later; the Cook–Levin reduction can emit the dense form directly).
* *Why dense:* the verifier compares clause row `j` against assignment bit `j` with a single
  synchronized scan, so no variable-index arithmetic is needed on a stack machine.

### NP verifier

Certificate alphabet `Γ₁ = Bool`, `k = 1`, `R w y := evalCNF w y [] false = true` where
`evalCNF` is a one-pass scan mirroring the machine (below). Pure-Lean lemmas: `R w y ↔
cnfSat (decodeCNF w) y`, and truncation `cnfSat φ a → cnfSat φ (a.take |w|)` (every clause has
width `< |w|`) gives the certificate bound `|y| ≤ |w|^1`.

### Verifier machine (`FinTM2`)

Stacks `Option W`, `W = inp | F | A | B`; `k₀ = some inp`, `k₁ = none` (output, alphabet
`Bool`); work stacks have alphabet `G = Bool ⊕ Option Bool` (= pair alphabet, identity
`inputAlphabet`). State `σ = Option G` (last popped symbol), initial `none`.

1. `read1`: move `w` from `inp` to `F` (reversed), consuming `#`.  `|w|+1` steps.
2. `read2`: move `y` from `inp` to `A` (reversed).  `|y|+1` steps.
3. `back1`: `F → inp` (restores `w`, head on top).  `|w|+1` steps.
4. `back2`: `A → B` (`y`, head on top).  `|y|+1` steps.
5. Main scan, labels `c0 fl`, `c1 fl b₁` read two bits; for a slot token move one assignment
   bit `B → A` and update `fl`; on `00` run `restore fl` (`A → B`, `≤|y|+1` steps), then reject
   if `fl = false`, else continue with `fl := false`. End of input ⇒ accept.
6. Cleanup (`haltList` needs every other stack empty and state reset): drain `inp`, `A`, `B`,
   then `finish ans` pushes `ans` on the output stack, resets state, halts.

Time `O(|w|·|y|) ≤ O(N²)` with `N = |w| + 1 + |y|`.

### Session log 2026-09-26 (SAT ∈ NP)

* Manifest verified first (see "Manifest check" above).
* Definition written here before any proof; implemented as specified with one change: the
  machine has an extra label `adv fl o` (one step per token to move an assignment bit), since a
  `pop` overwrites the state and the token's sign must survive in the label. Step count per
  token is 3, per clause end `|as| + 3`; total `totalSteps w y ≤ 2(|w|+|y|) + 5 + (|w|+1)(|y|+5)
  ≤ 2(n+5)²` with `n = |w|+1+|y|` (`T_le`, closed by `nlinarith`).
* Proof architecture: generic `loop_run` lemma (pop/transfer loops, used 8×) on a non-dependent
  view `stk V o` of the stacks (dependent `Function.update` was the main friction; isolating it
  in `update_stk_some` fixed that); one step lemma per scan label; `scan` by `evalCNF.induct`
  so the machine and the pure spec `evalCNF` are proved equal case by case; `evalCNF ↔ cnfSat`
  proved separately through an index-based `evalIdx`.
* Added imports `Mathlib.Tactic.DeriveFintype`, `Mathlib.Tactic.Linarith` (not in Millennium's
  import closure). No lakefile change.
* Banned-token scan of CookLevin.lean: only the `sorry` in `cook_levin` (plus the word in a doc
  comment). lean4checker still not run (owed before any READY FOR CHECK).
* Not started, per instruction: the hardness reduction, SatInP.lean.

---
---

# COOK–LEVIN HARDNESS: FORMALIZATION PLAN (scoping, 2026-09-27; awaiting review, no Lean written)

This section is separate from the SAT ∈ NP material above. Nothing here is proved. Effort
estimates are guesses. Plain framing: Cook–Levin is known mathematics; finishing it makes
**zero** progress on `sat_in_p`, which is the open problem. It is worth doing only as the honest
part (c) of the plan in `claude.md`.

## P1. Exact theorem, and what `ClayPVersusNP` structurally needs

Target (new name; `cook_levin` then becomes `⟨sat_in_np, sat_np_hard⟩`):

```lean
theorem sat_np_hard : ∀ {β : Type} (eb : FinEncoding β) (L' : Language β),
    InNondeterministicPolynomialTime eb L' →
    PolynomialTimeReducible eb (fin_encoding_string Bool) L' SAT
-- PolynomialTimeReducible eb _ L' SAT =
--   ∃ f : β → List Bool, ∃ _ : TM2ComputableInPolyTime eb.encode id f, ∀ b, L' b ↔ SAT (f b)
```

What the repo requires. `Solution.lean` uses
`ClayPVersusNP.nondeterministic_polynomial_time_complete_in_polynomial_time comp cook_levin sat_in_p`.
Its hypothesis is the full `NondeterministicPolynomialTimeComplete (fin_encoding_string Bool) SAT`,
whose definition (Millennium.lean:331) quantifies over **every** `FinEncoding eb`.

* **No repo lemma turns "hard for one encoding" into "hard for all encodings".** I checked the
  whole declaration list of Millennium.lean. The only completeness lemmas are
  `NondeterministicPolynomialTimeComplete.transfer` (moves completeness along a reduction) and
  `PolynomialTimeReducible.trans`.
* However, the *proof* of that repo theorem only uses `hComplete.2` at
  `fin_encoding_string alphabet'` with `[Fintype] [Nontrivial]` (Millennium.lean:1720–1729).
  So an alternative route exists: prove hardness only for string encodings and assemble
  `p_eq_np` via `ClassEquality.of_hard_direction_and_turing_machine_composition` + `source_in_p`.
  That route **changes Solution.lean's structure**, so it needs your approval.
* **Recommendation: prove the all-encodings version.** It costs almost nothing extra. The
  reduction only ever sees `eb.encode b : List eb.Γ`, and `eb.Γ` is a `Fintype` (possibly empty
  or a singleton, which is harmless). The NP verifier for `L'` is a machine over the pair
  alphabet `eb.Γ ⊕ Option Γ₁`. The construction below is parametric in that finite alphabet.
  Then `f b := Φ (eb.encode b)` and `L' b ↔ SAT (f b)` is proved per `b`. Solution.lean stays
  unchanged.

## P2. Size of the output formula (explicit bound)

Notation (all constants depend only on the fixed NP verifier `M`, not on the input):
* `n = |eb.encode b|` (the reduction's input length); certificate bound `N = n^k`.
* The verifier input is `w # y` with `|y| ≤ N`, so its length `m ≤ n + 1 + n^k ≤ 2(n+1)^{k'}`,
  where `k' = max k 1`.
* Verifier time `p` (a `Polynomial ℕ`). With `e = natDegree p` and `P = Σ coeffs`,
  `p(x) ≤ P·(x+1)^e`. Let `E = max e 1 · k'`. The run length is then
  `T := p(max input length) ≤ t₀ (n+1)^E`.
* Stack cap `H = m + (T+1)·d + 1 ≤ h₀ (n+1)^E`, where `d = depth M` (Sit.lean: the maximum number of
  pop/peek/push operations on one path of one statement tree). Lean: `Sit.capH m T d` (2026-09-30).
  *Correction (2026-09-30, sixth session):* this line used to read `H = m + c·T + d + 1` with
  `c = pushBound M`. That was wrong for the tableau: the height bound actually used by C2/C6
  (`stepI_height`) grows by `depth M` per step, not `pushBound M`, and `depth M > pushBound M` is
  possible (exM: 6 > 4), so the old `H` failed `ℓ + (T+1)·depth M ≤ H` (witness `exM_H_fails_c1`,
  ScratchH.lean). The new `H` is still polynomial in `n` (same exponent `E`).
* `K` stacks; `g` = max effective alphabet size + 1 (for ⊥); `A = |Λ| + 1 + |σ|`.

Variables: `V = (T+1)·(A + K·H·g) ≤ v₀ (n+1)^{2E}`.

Clauses, by family, with `S₀ = |Λ|·|σ|·g^{dK}` the number of "situations" (a constant):
* one-hot (at least one + pairwise at most one): `(T+1)(K·H·(1+g²) + A²)`
* transition: `T·S₀·K·H·g`, plus `2·T·S₀` for label/state updates
* halted-idle: `T·(K·H·g + A)`
* initial (`w` fixed, `#`, certificate cells free) + final (accept): `O(K·H·g + A)`
* total `C ≤ c₁ (T+1) H ≤ c₀ (n+1)^{2E}`.

The dense encoding (`encodeCNF`) costs `2(V+1)` bits per clause, so
**bits `B = 2·C·(V+1) ≤ b₀ (n+1)^{4E}`: polynomial, of degree `4E`.**

* Compared with a sparse encoding (`≈ C·w·log V` bits, where `w` is the constant clause width),
  the dense form costs an extra factor of about `V / log V ≤ (n+1)^{2E}`. That is polynomial.
* The reduction machine's running time must be at least `B`. A naive generator that walks all
  `V` slots per clause and does `O(V)` counter work per slot runs in
  `O(C·V²) = O((n+1)^{6E})`, still polynomial.
* The SAT side adds no compounding: `sat_in_np`'s check machine is not part of the reduction.

**Conclusion:** the dense encoding composes with polynomial blowup. The concern from last
session is settled, with exponent `4E` for size and `≤ 6E` for generation time.

## P3. Model decision (the main design bet)

**Index each stack from its TOP and pad with ⊥ up to depth `H`.** In the TM2 model one step runs
one statement tree. That tree reads at most the top `d` symbols of each stack, pops at most `d`,
and pushes a bounded list (pushed symbols come from `σ`). So stack `k` at time `t+1` is:
positions `< |pushed|` get the pushed symbols, and every other position `j` gets the symbol from
position `j − |pushed| + pops` at time `t`. That is a **shift by a constant `δ ∈ [−d, d]`**,
decided entirely by the "situation" (label, state, top-`d` windows of every stack).
Consequences:

* **No head position and no height variables.** The situation's variables are always at the
  fixed positions `0..d−1`. The transition constraint is a single clause family:
  `situation(t) ∧ C[t,k,j−δ,x] → C[t+1,k,j,x]`.
* **Variable-length certificates need no padding trick.** With top-indexing, `w` sits at the
  fixed positions `0..|w|−1` of the input stack and `#` at `|w|`. Certificate cells at `|w|+1+i`
  range over `Γ₁ ∪ {⊥}`, with the constraints "once ⊥, stays ⊥" and "⊥ at every `i ≥ N`".
* **Non-finite work alphabets are handled.** Only `Γ k₀` is `Fintype`. Every other symbol on a
  stack was pushed by some `push k f` with `f : σ → Γ k`, so it lies in a finite, classically
  defined set `Γfin k`. Lean definitions may be noncomputable: `TM2ComputableInPolyTime` only
  needs a `FinTM2` to *exist*, and its finite tables can be defined classically.
* **The halting convention helps.** Acceptance = label `none` ∧ output stack exactly `[true]`,
  which is a fixed-position check.

## P4. Sub-lemma list

Difficulty: **M** mechanical, **Mo** moderate, **H** hard. "Deps" lists the existing definitions
or lemmas used.

### A. Plumbing

| # | Name | One-line statement | Diff. | Deps |
|---|---|---|---|---|
| A1 | `cook_levin` (reassembled) | `⟨sat_in_np, sat_np_hard⟩` | M | repo `NondeterministicPolynomialTimeComplete` |
| A2 | `np_unpack` | `InNP eb L'` gives `Γ₁, R, k`, a verifier `V : TM2ComputableInPolyTime (pair_encoding eb (fin_encoding_string Γ₁)).encode finEncodingBoolBool.encode fR`, and membership | M | repo `InNondeterministicPolynomialTime`, `pair_encoding` |
| A3 | `run` / `run_eq_haltList` | idle-extended run `run c t` (halted configs fixed); for `t ≥ steps`, `run (initList x) t = haltList [fR x]` | Mo | Mathlib `EvalsTo`, `TM2.step`; Comp `iter_none` |
| A4 | `run_deterministic` | two runs reaching halted configs from the same config agree | M | `Function.iterate` |
| A5 | `height_le` | ~~every stack of `run c₀ t` has length `≤ m + c·t`~~ **superseded 2026-09-30:** `Sit.runI_height` (`≤ |c₀| + t·depth M`, idle-extended run) + `Sit.capH_height` (`≤ capH m T d − d` for `t ≤ T`), **proved** | M | ~~reuse Comp `length_iter`, `pushBound`~~ not needed: `pushBound` bounds growth by pushes only, but the tableau needs `H − d` slack, and the depth-based bound matches `stepI_height` |

### B. Locality of TM2 steps (model-specific; no blueprint counterpart)

| # | Name | One-line statement | Diff. | Deps |
|---|---|---|---|---|
| B1 | `stepAux_local` **(DONE 2026-09-30: `eff_agree`, `step_agree`, `Enc.table_agree`)** | **(sharpened 2026-09-27 per P7)** `stepAux q v S = ⟨l', v', fun k => P k ++ (S k).drop (j k)⟩`, with `(l', v', j, P)` a function of `(q, v, fun k => (S k).take d)` only. Here `j k` = **net original symbols consumed** from stack `k` (a push followed by a pop of that pushed symbol cancels; `j` is NOT the raw number of `pop` statements) and `P k` = symbols pushed this step that are still on top at the end. `d` must bound `j k` **and** the depth of every peek/pop that reads below the symbols pushed this step; a sufficient choice is `d := ` max number of `pop`/`peek` nodes on any root-to-leaf path of any statement tree of the machine. Holds unconditionally (short stacks: `take d` is the whole stack); the height precondition `≤ H − d` belongs to C2, not B1 **(2026-09-28, shift family:) `d` must also bound `(P k).length`, the pushes still on top, i.e. `d := max(deepest read, max |P k|)`** | Mo | Mathlib `TM2.stepAux`, `TM2.Stmt`; P7 spike (evidence only) |
| B2 | `Γfin`, `run_mem_Γfin` **(DONE: `symSet`/`Enc.ofFinTM2` 2026-09-29, `Enc.run_good` 2026-09-30)** | finite effective alphabets; every symbol on stack `k` along the run lies in `Γfin k` | Mo | `FinTM2.σFin`, `Finset.image` (classical) |
| B3 | `Situation`, `sitStep` | the finite type of (label, state, windows) and its induced (new label, new state, δ, pushed) | M | B1, B2, `Fintype` instances |

### C. Tableau combinatorics (pure Lean; analogue of GK "TMGenNP → CC → SAT", Balbach `Reducing`)

| # | Name | One-line statement | Diff. | Deps |
|---|---|---|---|---|
| C1 | `cells`, `decodeCells` **(DONE 2026-09-30: `Enc.code`/`Enc.cell`, `Enc.decRow`, `decRow_enc`, `enc_decRow`, `cell_rowOK`, `row_inj`; Sit.lean [C1])** | top-indexed, ⊥-padded arrays of a config and back; round-trips on prefix-form arrays of height `≤ H` | M | B2 |
| C2 | `cells_step` **(DONE 2026-09-30: `Enc.table_agree` on `Enc.cell`; decoded form `Enc.decRow_tabRow`, a 5-line corollary)** | if all heights are `≤ H−d`, then `cells (step c)` is the δ-shift/fill of `cells c` given by `sitStep` | **Mo/H** | B1, B3, C1 |
| C3 | `Var`, `varIdx` | finite variable type (label/state/cell one-hots per time step) and an injective numbering `< V` | M | — |
| C4 | `Φ` (abstract, sparse) | clause families: one-hot, init (`w` fixed, `#`, free certificate cells with prefix form and `≤ N`), transition, idle, accept | Mo | C3, B3 |
| C5 | `Φ_complete` | `R w y` with `|y| ≤ N` → the assignment read off the real run satisfies `Φ` | Mo | A3, A5, C1, C2 |
| C6 | `Φ_sound` | assignment satisfies `Φ` → the decoded certificate `y` has `|y| ≤ N`, and the decoded rows are the real run on `w # y`, which accepts, so `R w y` | **H** | A3, A4, C1, C2, one-hot decoding |
| C7 | `toDense_sat` | the sparse `Φ` rendered as a dense `CNF` over `V` variables: `cnfSat (toDense Φ) a ↔ Φ-sat` | M | `SATDef.cnfSat`, `decodeCNF_encodeCNF` |
| C8 | `size_bound` | `(encodeCNF (toDense Φ)).length ≤ b₀ (n+1)^{4E}` (P2) | M | `Polynomial.eval` bounds (Comp `eval_mono`) |

### D. The reduction is `TM2ComputableInPolyTime` (analogue: Balbach `Composing`/`Memorizing`/`Aux_TM_Reducing`/`Reduction_TM`; GK used L-extraction + time-bound automation, which **does not exist** here)

| # | Name | One-line statement | Diff. | Deps |
|---|---|---|---|---|
| D1 | `Prog` library | in-machine sequencing, unary counters (copy, compare, decrement), nested for-loops, and emit, each with an exact step-count lemma (generalizes `Verifier.loop_run` / the `stk` view) | **H** (infrastructure) | CookLevin.lean `loop_run`, `Run`, `stk` pattern |
| D2 | `unaryBound` | a machine writing `1^{t₀(n+1)^E}` and `1^{h₀(n+1)^E}` (monomial over-approximations, so no general polynomial evaluator is needed) | Mo | D1 |
| D3 | **`generator`** | a `FinTM2` that, on input `s`, halts with `encodeCNF (toDense (Φ s))` on its output stack | **H: the hardest** | D1, D2, C4, C7, hard-wired finite tables from B3 |
| D4 | `generator_time` | step count `≤ poly(n)` (≈ `(n+1)^{6E}`) | Mo | D1, C8 |
| D5 | `sat_np_hard` | package: `f := toDense ∘ Φ ∘ eb.encode`; the alphabet equivs are `Equiv.refl`; correctness from C5, C6, C7 | M | A2, D3, D4 |

### What transfers from the blueprints

**Transfers (as structure, not code):**
* The pipeline "generic NP problem for a fixed machine → tableau → local constraints → CNF"
  (GK's `TMGenNP → CC → BCC → FSAT → SAT`; Balbach's `Reducing`).
* Splitting correctness into completeness (C5) and soundness (C6).
* Guessing the certificate as free initial cells. GK prepend a guessing line; here the free
  cells sit directly in row 0.

**Does not transfer, and is simpler here:**
* GK reduce multi-tape → single-tape (a large compiler) and then fight head position and blanks.
  Their paper reports 100 non-contradictory cases for its Theorem 14, handled with custom Ltac.
  With top-indexed stacks the step is a constant shift: no multi-to-single-tape step and no head
  variables.
* Balbach first makes the verifier *oblivious* (the `Oblivious*` theories) so that head positions
  are input-independent. That is not needed here, for the same reason.
* GK's and Balbach's intermediate problems (CC, BCC, FSAT) are unnecessary. The clause width is
  a constant, so CNF can be emitted directly.

**Does not transfer, and is harder here: poly-time computability of the reduction.**
* GK get it "for free" from 17k+ lines of reused L-extraction libraries.
* Balbach builds TMs by hand on top of a composition library.
* **We have neither**, only `PvsNP.comp` (composition of whole machines) and one ad-hoc loop
  lemma. D1–D4 is Balbach-style work in a model with no library.

**Evidence for the effort split.** GK Table 1 (spec + proof lines, Coq): TMGenNP → CC
3470 + 4442; CC → SAT 755 + 2312; SAT ∈ NP 108 + 297; libraries 17000+ each for spec and proof.
The Balbach AFP entry has 18 theories; the reduction-TM theories (`Aux_TM_Reducing`,
`Sat_TM_CNF`, `Reduction_TM`) plus the TM-building infrastructure look like a large share, but I
did not verify its line counts.

## P5. The hardest sub-lemma

**D3 `generator`: an explicit `FinTM2` that emits the dense CNF, proved correct.** It must:
* recompute `T`, `H` and `N` in unary from `n`;
* run nested loops over (time, stack, position, symbol, situation);
* for every clause, walk all `V` slots and put literals at index tuples tied to the loop counters
  (`t` vs `t+1`, `j` vs `j−δ`), which needs counter comparisons that do not destroy the counters.

Our only data point: a 12-label scan with no counters (the SAT verifier) took ~520 lines of
machine proof.

It is also the sub-lemma most likely to expose a real problem with the approach. If a
machine-level proof of this size is infeasible without a real program library (D1), the plan's
shape is wrong. We would then first build a verified mini-language → `FinTM2` compiler with a
cost semantics, which is a multi-session project of its own.

**Proposed first formalization step:** a spike on D1 plus a toy D3 (emit the one-hot clause
block for a given `n`), to measure lines per construct before any of C is written.

Highest *mathematical* risk (as opposed to volume): **C6 soundness**, together with C2. Both
rely on the top-indexed shift model; if B1 locality has a gap, it will show up in C2/C6.

## P6. Scope estimate

| Block | Est. Lean lines | Basis |
|---|---|---|
| A (plumbing) | 300–500 | similar to Comp.lean's glue sections |
| B (locality) | 600–1000 | `stepAux` inductions like Comp's `stepAux_lift₁` and `length_stepAux` |
| C (tableau) | 3000–5000 | GK's C-part is ~11k lines including multi-tape/blank handling; our shift model is simpler |
| D (computability) | 4000–9000 | the SAT verifier is ≈ 520 lines for a trivial scan; the generator has ~10–20× the logic, partly offset by the D1 library |
| **Total** | **~8k–15k lines** | vs. the current CookLevin.lean (800 lines) and Comp.lean (~600). **REVISED 2026-09-27 (third session): ≈ 11k–16k, D block ≈ 7k–9.5k — see "D1 EXTENSION + D3 PARAMETRIC FAMILY". REVISED 2026-09-28: ≈ 10.5k–16k, D block ≈ 6.6k–9.6k — see "FINITE LABELS + TIME BOUND"** **REVISED 2026-09-28 (third): ≈ 11.4k–17.0k, D block ≈ 7.3k–10.0k — see "CELL-SHIFT FAMILY"** **REVISED 2026-09-29: ≈ 10.7k–15.5k, D block ≈ 6.6k–8.5k, ≈ 8–13 more sessions (remaining lines, corrected method) — see "SITUATION VARIABLES: DESIGN FIXED"** **REVISED 2026-09-29 (third): ≈ 10.7k–15.15k, B block measured (≈ 0.46k of 0.65k–0.9k), ≈ 7–12 more sessions — see "B3: SITUATION TABLES"** |

At roughly 600–900 verified lines per session (the last two sessions), that is
**~12–25 sessions**. D3 is the largest uncertainty and could double this.

Suggested order: D1 spike + toy D3 → B → C2 → C4/C5 → C6 → D2–D5 → A → reassemble
`cook_levin` and re-run `#print axioms`.

## Open decisions for review

1. **Encodings:** all encodings (recommended; Solution.lean unchanged) vs. strings only
   (Solution.lean restructured).
2. **Generator:** build the D1 library first (recommended) vs. write the generator as a raw
   `FinTM2`.
3. **SAT encoding:** keep the dense encoding (recommended; P2 shows it is polynomial) vs. switch
   to a sparse one. Switching would make D3's output smaller but forces redoing `sat_in_np`
   (~800 lines).

## P7. Soundness spike for P3 (2026-09-27) — outcome: NO MISMATCH

Scratch file `Spike.lean` (**non-canonical**: not in the lakefile roots, not imported, proves
nothing the development uses). It implements the P3 model literally. `eff` computes, from ONLY
the label, the state and the top-`d` cells of each stack, a new label, a new state, and per
stack `(P, j)`, where `P` = symbols pushed and still on top and `j` = original symbols consumed.
`shiftCells` then moves cells positionally without reading them. The result is compared with
Mathlib's real `TM2.step`.

| Test | Cases | Mismatches |
|---|---|---|
| Toy machine, 1 step, exhaustive (3 labels × 3 states × 11 × 11 stack contents, `d=2`, `H=8`) | 1089 | 0 |
| Toy machine, runs up to 6 steps, model iterating on its own cells only (`H=12`) | 1089 | 0 |
| SAT verifier (`PvsNP.Verifier.prog`), 1 step, exhaustive (30 labels × 6 states × 6⁴ work stacks × 3 outputs, `d=2`, `H=6`) | 606528 | 0 |
| SAT verifier, full run on input `10 00 # 1`, 40 steps, model on its own cells (`H=16`) | 1 | agree (`true`) |
| 5 stress instances, **kernel-checked by `decide`** | 5 | 0 |

The toy machine covers:
* height 0 (pop and peek on an empty stack);
* push-then-pop of the same stack within one step;
* push, then peek, then pop of the pushed symbol, then pop of an original symbol;
* attention moving from one stack to another (pop `a`, push twice on `b`);
* branching on popped values.

Negative controls (the model *should* fail when a precondition is violated, and it does):
* window `d = 0` → `false`;
* cap `H = 1` with height 2 → `false`;
* the same config with `H = 4` → `true`.

Clarifications this forces on P3's wording (not design changes):
* The shift offset uses `j` = **net original symbols consumed**, not the number of `pop`
  statements. A push-then-pop cancels. B1 must be stated this way.
* `d` must bound `j` plus the depth of any peek or pop read below the pushed prefix. The
  number of pop/peek nodes on a path in the statement tree is a sufficient `d`.
* Precondition: every height `≤ H − d`. The spike confirms the model is wrong without it (P2's
  `H = m + c·T + d + 1` already provides it). [**2026-09-30 correction:** the old formula did not provide this when `depth M > pushBound M`; P2 now uses `H = m + (T+1)·d + 1`, and `Sit.capH_height` proves the height precondition for it. See "H CORRECTION + DEPTH_COVER ASSEMBLY".]

Evidence status: `#eval` counts are evidence, not proof. The 5 `decide` examples are
kernel-checked but concrete. The general statement is still B1/C2, which are not started.

---

# D1 LIBRARY — built 2026-09-27 (Prog.lean) + toy D3 trial (ToyD3.lean, scratch)

## Which sub-lemmas are D1

Of the 21 sub-lemmas (A1–A5, B1–B3, C1–C8, D1–D5), **only D1** ("`Prog` library") is D1. D2
(`unaryBound`) uses D1 but is a separate item and has not been started. D1 was split into the
primitives below. All are generic over `{K} [DecidableEq K] {Γ : K → Type} {Λ σ}` and any
`M : Λ → TM2.Stmt Γ Λ σ`. Branching needs one bit of state, `[Flag σ]` (`tag : Bool → σ`,
`untag`, `untag (tag b) = b`). A primitive occupies labels; its lemma takes `hp : M self = …`,
discharged by `rfl`.

| # | Primitive | Signature (exact up to notation) | Steps |
|---|---|---|---|
| D1.0 | `Run M n c d`, `Run.zero/head/trans/of_eq/single` | `(flip bind (TM2.step M))^[n] (some c) = some d`; sequencing = `Run.trans` | — |
| D1.1 | `cnt u n := List.replicate n u` | a counter is a stack holding exactly `u^n` | — |
| D1.2 | `incr k u next`, `decr k ifZero ifPos` | `incr_run(_cnt)`: `→ ⟨next, v, update S k (u :: S k)⟩`; `decr_run_cnt`: `S k = cnt u (n+1) → ⟨ifPos, tag true, update S k (cnt u n)⟩`; `decr_run_zero`: `S k = [] → ⟨ifZero, tag false, S⟩` | 1 |
| D1.3 | `xfer k ps self next` (`ps : List (Σ k, Γ k)`) | `ps.NodupKeys → k ∉ ps.keys → S k = cnt u n → Run (n+1) ⟨self,v,S⟩ ⟨next, tag false, addU ps n (update S k [])⟩` (drain: `ps=[]`, move: one target, copy: two targets) | `n+1` |
| D1.4 | `cmpStep` + `cmp_run` | stacks `a,b,ta,tb` pairwise distinct, `S a = cnt ua m`, `S b = cnt ub n`, `S ta = S tb = []` → `Run (3·min m n + 3 + [m≠n]) ⟨self,v,S⟩ ⟨out (compare m n), tag false, S⟩`. **Non-destructive:** all stacks are restored | `3·min+3(+1)` |
| D1.5 | `forHead c cd ucd body rest` + `forLoop_run` | Inputs: an invariant `P i S` that does not depend on `c, cd`, and a body contract: for every `i<n`, from `⟨body, tag true, S⟩` with `c = n-1-i`, `cd = i+1` and `P i S`, the body reaches `⟨head,…⟩` in `cost i` steps, preserves `c` and `cd`, and establishes `P (i+1)`. Then from `c = n`, `cd = []`, `P 0`: `∃ S', Run (sumFrom (cost·+1) 0 n + n + 2) … ⟨next, tag false, S'⟩ ∧ S' c = cnt uc n ∧ S' cd = [] ∧ P n S'` | as stated |
| D1.6 | `emit k xs next` | `Run 1 ⟨self,v,S⟩ ⟨next, v, update S k (xs.reverse ++ S k)⟩` | 1 |
| D1.7 | `sumFrom`, `sumFrom_const`, `sumFrom_le` | cost accounting: `(∀ t ∈ [i,i+j), f t ≤ c) → sumFrom f i j ≤ j·c` | — |

Nested loops are a `forLoop_run` whose body contract is discharged by another `forLoop_run`;
the toy exercises this. A non-destructive copy is two `xfer`s (`c → [d, tmp]`, `tmp → [c]`).

## Build log (one primitive at a time; each checked with `lake env lean Prog.lean`, ~26–33 s)

`lake build` does not see Prog.lean because it is not in `roots`. Adding it is a lakefile
change, which needs approval. So each step was checked by elaborating the file directly.

| Step | Primitive | Result | Fix rounds |
|---|---|---|---|
| 0 | `Run` + sequencing | clean | 0 |
| 1 | counter type | clean | 0 |
| 2 | `incr`/`decr` | clean | 1 (simp normal form in `decr_run_zero`) |
| 3 | `xfer` (+ `pushAll`, `addU` algebra) | clean | 2 (combinator misuse; redundant tactics) |
| 4a | `cmpLoop_run` | clean | 3 (wrong final flag in `lt` case; `compare` not reducing; redundant `rfl`s) |
| 4b | `cmp_run` (with restores) | clean | 1 (unsynthesizable state argument) |
| 5 | `forLoop_run` | clean | 1 |
| 6 | `emit` | clean | 0 |
| 7 | `sumFrom_le` (added for the toy's time bound) | clean | 0 |

Final state:
* Prog.lean is 518 lines.
* `lake build` of the canonical roots still succeeds (1257 jobs). The only warnings are the
  known `sorry`s in Challenge.lean, `cook_levin` and `sat_in_p`.
* **No cost surprise.** The most expensive primitive was `cmp` (~150 lines including the
  restores), in line with the "H (infrastructure)" estimate. All of D1 is ≈ 520 lines, about
  what the hand-written SAT verifier needed on its own.

`#print axioms` for every D1 declaration:
* No axioms: `Run`, `Run.zero`, `Run.head`, `Run.of_eq`, `cnt`, `cnt_zero`, `cnt_succ`, `incr`,
  `decr`, `pushAll`, `addU`, `xfer`, `cmpStep`, `sumFrom`, `forHead`, `pushList`, `emit`.
* `[propext]`: `Run.trans`, `Run.single`, `cnt_length`, `cnt_add`, `cnt_injective`, `incr_run`,
  `decr_run_pos`, `decr_run_cnt`, `addU_single_self`, `addU_single_ne`, `single_nodupKeys`,
  `sumFrom_const`.
* `[propext, Quot.sound]`: `incr_run_cnt`, `addU_addU`, `compare_succ_succ`.
* `[Quot.sound]`: `addU_zero`.
* `[propext, Classical.choice, Quot.sound]`: `decr_run_zero`, `addU_of_not_mem`, `addU_update`,
  `stepAux_pushAll`, `xfer_run`, `cmpLoop_run`, `cmp_run`, `forLoop_run`, `stepAux_pushList`,
  `emit_run`.
* `sumFrom_le` was added after that run. It has no separate `#print axioms`; it is used by
  `toyTime_le`, whose axioms are the standard three.

## Toy D3 trial (ToyD3.lean)

ToyD3.lean is SCRATCH and throwaway: not a root, and it has no `import`. It is checked by
concatenating `import Mathlib.Tactic.Linarith`, Prog.lean and ToyD3.lean into one file.

Task: from `n` in unary, emit the dense-CNF bits of `⋀_{i<n} ¬x_i` as `n` clauses of width `n`.
* Machine: 8 stacks (7 unit counters and a Bool output); 11 label constructors, 3 of them
  indexed by `Ordering`, so 17 labels.
* Constructs: 1 `xfer`, 2 nested `forLoop`s, 1 `cmp` of the two loop indices, 3 `emit`s.

Proved (axioms `[propext, Classical.choice, Quot.sound]`; banned-token scan clean):
* `toy_run n : ∃ S', Run prog (toyTime n) ⟨start, false, init n⟩ ⟨done, false, S'⟩ ∧
  S' out = (diagBits n n).reverse`
* `toyTime_le n : toyTime n ≤ 10·(n+1)³`
* spec sanity check: `diagBits 2 2 = 11 01 00 01 11 00`, by kernel `decide`.

**Measurement:** 119 non-comment lines in total.
* Breakdown: machine and types ≈ 25, spec 12, inner body 20, outer body 25, top level 20, time
  bound 15.
* Two fix rounds: the dependent alphabet `TΓ` must be an `abbrev`, and `NodupKeys` is not
  decidable (use `simp`).
* **Cost per construct:** ~20–25 lines per loop level, ~3–6 lines per primitive use, ~5 lines of
  frame boilerplate per loop invariant.
* Against the library-less SAT verifier (~520 lines for a 12-label scan), that is roughly a 4×
  reduction per label.

## What the measurement says about D3 (revised estimate)

D3 needs the following, which the toy did not measure:
1. **Index arithmetic.** Literal positions `varIdx(t,k,j,x)` need unary addition and
   multiplication of counters. Each slot also needs comparing the slot counter against several
   literal indices. Estimate: +300–500 lines of library (D1-style).
2. **Iteration over abstract finite types** (the verifier's situations, symbols and stacks):
   label families indexed by `Finset.univ.toList` suffixes, with correctness by list induction.
   Estimate: +200–400 lines.
3. **Parametric machine.** The toy is concrete (`decide` for stack distinctness, `rfl` for
   program equations), but D3 is parametric in the verifier. That overhead is unmeasured and is
   the largest remaining unknown.
4. **Frame boilerplate** grows with the number of stacks times the number of invariant
   conjuncts. The toy had 8 stacks and 5-conjunct invariants; D3 may have 20+ stacks.
   Mitigation to try first: state invariants as "agrees with a reference `S₀` off the touched
   stacks" (a D1 extension).
5. **Output order and a clean halt.** Emission reverses the output. Generating in reverse order
   avoids a symbol-preserving reverse copy, since the down-counter `c = n-1-i` is available
   inside every loop. Clean-up drains use `xfer _ []`.

Revised D-block estimate:
* ~6 clause families × 400–600 lines, plus 500–900 for items 1–2, ~300 for D2, ~300 for the D4
  bounds and 520 for D1 (done) ≈ **4.0k–5.6k lines**.
* That is the lower half of P6's range (4k–9k), *provided* item 3 does not blow up.
* Overall total revised to **~7.5k–12k lines** (P6: 8k–15k).
* This extrapolates from one concrete toy; it is not a measurement of D3.

## Open request

Add `"Prog"` to `roots` in `lakefile.toml` so that D1 is covered by `lake build` and can later
be imported by the generator. Not done yet: lakefile changes need approval.

---

# D1 EXTENSION + D3 PARAMETRIC FAMILY (session of 2026-09-27, third)

## Lakefile

Approved change applied: `roots = [..., "Solution", "Prog"]`. `lake build` → `✔ Built Prog`,
`Build completed successfully (1260 jobs)`. Only the known `sorry`s (Challenge.lean,
`cook_levin`, `sat_in_p`) remain. D3Fam.lean is **not** a root (exploratory; checked with
`lake env lean D3Fam.lean`).

## D1 extension (Prog.lean, KEPT as library): 518 → 854 lines (+336)

Estimate was +300–500. Each primitive was checked on its own; all are clean.

| Primitive | Statement | Steps | Fix rounds |
|---|---|---|---|
| `copy_run` | `c += a` through an empty scratch `t`; `a` restored | `2m+2` | 0 |
| `add_run` | `c += a + b` | `2m+2n+4` | 0 |
| `mul_run` | `c += a·b` (a `forLoop` over `a` with body `copy b → c`); all stacks except `c` restored; distinctness is a single `[a,ad,b,c,t].Nodup` | `m(2n+3)+m+2` | 1 |
| `rep`, `emitR` | `emitR` prepends a list (`ys ++ S k`) | 1 | 0 |
| `xferE_run` | drain a counter of value `n`, prepending `rep ys n` onto another stack | `n+1` | 0 |
| `emitDiff_run` | gap emission: from `P = q+gap+1`, `Q = q`, decrement `P` and compare to `Q` until equal, prepending `ys` each time; ends with `P = q` | `gap(3q+6)+3q+4` | 3 |
| `Reach`, `Reach.trans/refl/of_eq`, `Run.reach`, `forLoop_reach` | runs of unspecified length; a `for` loop whose body cost is data-dependent | — | 0 |

## The parametric clause family (D3Fam.lean, 899 lines, EXPLORATORY)

**Family:** the label/state-update part of P2's transition clauses. For every `t < T` and every
situation `i < N`:
`¬X[t, la i] ∨ ⋁_{k<KK, j<d} ¬C[t,k,j, wa i k j] ∨ X[t+1, na i]`.
* Each clause is a *dense* clause over all `V = (T+1)·W` variables, encoded with the real
  `SATDef.encodeClause`/`encodeCNF`.
* Draft C3 layout: `W = A + KK·H·g`, `X[t,a] = t·W + a`, `C[t,k,j,x] = t·W + A + (kH+j)g + x`.
* Symbolic parameters: `A, KK, g, d` and the tables `la, na : ℕ → ℕ`, `wa : ℕ → ℕ → ℕ → ℕ`.
* Runtime inputs, in unary: `T` and `H`.
* The only hypothesis is well-formedness `WF`: codes in range and `d ≤ H`.

**Main theorem** (axioms `[propext, Classical.choice, Quot.sound]`):
```
gen_correct (T H) (hwf : ∀ i < N, WF L la na wa H i) (o) :
  ∃ v S, Reach (prog L la na wa N) ⟨pre.eg, false, st (initF T H) o⟩ ⟨done, v, S⟩ ∧
         S .out = encodeCNF (family L la na wa T H N) ++ o
```

**Machine:** 15 unit-counter stacks plus the Bool output. Its phases:
* Precompute: `g`, `H·g`, `W`, `V = (T+1)W`.
* Time loop: `forLoop_reach` over `T`, processing `t` in descending order; each step computes
  `TW = t·W`.
* Situations: `i = N-1 … 0`, iterated through the label parameter.
* Literals: `j = nLits-1 … 0`, iterated through the label parameter. For each one:
  `Q := TW + kA·(H·g) + kB·W + cst` via `copy`, `mul`, `emit`; then `emitDiff` from the previous
  boundary; then the literal slot; then `xferE` for the leading gap.
* Everything is prepended, so the output comes out in the right order without a reversal pass.

**Evidence (not proof):** `#eval` of the real machine on 8 concrete instances matched
`encodeCNF (family …)` exactly. The instances include `KK=0`, `d=0`, `N=0` and `T=0`; up to
28718 steps and 768 output bits.

### Section costs (lines) and fix rounds

| Section | Lines | Reusable for other families? | Fix rounds |
|---|---|---|---|
| layout + spec (`litPos`, `lits`, `denseClause`, `family`) | 83 | layout yes; spec per family | 0 |
| block decomposition (`gapEnc`, `Inc`, `encodeClause_denseClause`, `gapEnc_shift`) | 80 | **yes, fully generic** | 1 |
| sortedness (`litPos_mono`, `lits_inc`; nonlinear, with `/` and `%` by `d`) | 120 | no (per family) | 3 |
| machine definition | 107 | pattern yes | 0 |
| `st` view of the stacks (non-dependent counters) | 59 | **yes** | 0 |
| `lit_run` (11 chained primitives) | 94 | yes for any literal whose position is affine in `(H·g, W)` | 2 |
| clause level (`litPos_eq`, `lits_drop`, `bnd`, `inc_drop`, `lits_run`, `clause_run`) | 157 | mostly | 2 |
| situations, time loop, precompute, `gen_correct` | 199 | skeleton yes | 4 |

### Did `decide`/`rfl` automation survive? (the question for this session)

* **Program equations: yes, `rfl` everywhere**, including labels that carry the symbolic
  situation/literal numbers `i, j` and the symbolic tables (e.g. `prog (.lit i j (.r o)) = xfer
  …` for variable `o`). Reason: the generator's labels are constructors and `prog` unfolds
  definitionally whatever the parameters are.
* **Stack distinctness: yes, `decide`.** The generator's *own* stacks are a fixed concrete type
  (`CK`); the verifier's finite types enter only as *numbers* (`KK, g, d, A`) and tables, never as
  generator stacks. So the feared "distinctness not free" problem does not arise in this design.
* **Counter bookkeeping: automated** by the `st f o` view. Every state is `st f o` with
  `f : CK → ℕ`, and final-state equalities close by `funext x; cases x <;> simp`.
* **Real proof work was needed for:**
  * (a) list/encoding algebra: dense clause = gap/literal blocks (generic, done once);
  * (b) nonlinear index arithmetic with `/` and `%` for sortedness (per family; the costliest
    per-family piece);
  * (c) the invariants of the data-dependent loops (literal and situation loops by induction
    over label parameters; the time loop through `forLoop_reach` with an output invariant over
    `List.range'`).

### Compared with the toy's cost per construct

| Measure | Toy (concrete) | This family (parametric) |
|---|---|---|
| per primitive use | 3–6 lines | ~8.5 lines (`lit_run`: 11 uses in 94 lines) |
| per loop level (incl. invariant) | 20–25 lines | ~60–150 lines (literal loop ~60, situation loop ~25, time loop + invariant ~70, plus per-level sortedness/`Inc` plumbing) |
| whole family | 119 lines | 899 lines, of which ~300 are reusable infrastructure |

So a real family costs **~5–7× the toy** (≈ 600 family-specific lines). That is not because
automation broke. The reason is the real content: dense-clause block structure, index
arithmetic, and invariants of data-dependent loops.

### Not covered this session (explicitly unmeasured)

1. **Finite labels.** `GL` carries `ℕ` parameters (`i`, `j`), so it is not a `Fintype`, and a
   `FinTM2` needs one. The fix is to bound them by `N` and `nLits` (`Fin`/subtype). Goto targets
   then need proofs. Estimate +150–250 lines per generator, one-time.
2. **Time bounds.** Only `Reach` (existence of a run) is proved. D4 needs polynomial step
   bounds. All primitives have exact counts, but threading bounds through every `Reach` step
   is new work. Guess: +40–60% on each family's correctness proof. Not measured.
3. **Connection to the real verifier.** The tables `la, na, wa` and the layout constants are
   abstract. Deriving them from the verifier's situations (B2/B3) is a reindexing, not done.
   The layout here is a *draft* C3.
4. **Families with runtime inner loops** (cell one-hot over `j < H`, cell shifts by `δ`) and the
   input-reading init family (a new primitive: read an input symbol into the label). Not
   attempted.

### Keep or supersede?

* **Prog.lean additions: KEPT** (library, a lakefile root).
* **D3Fam.lean: partly kept, partly superseded.**
  * Kept, to migrate into the real D3/C files: the block decomposition (`gapEnc`, `Inc`,
    `encodeClause_denseClause`, `gapEnc_shift`, `inc_of_mono`), the `st`-view pattern, and the
    literal-routine design (`lit_run`).
  * Expected to be **superseded**: the draft layout (until C3 is fixed), the `ℕ`-indexed labels
    (item 1), `Reach` in place of bounded runs (item 2), and the abstract tables (item 3).
  * The file is exploratory and is not imported by anything.

## Revised scope estimate (supersedes the "~7.5k–12k" of the D1 session)

That extrapolation came from one concrete toy and **understated D**. The per-family
measurement above gives:

| Block | Estimate | Basis |
|---|---|---|
| D1 library | 854 (done) | measured |
| D3 families | 6–8 families × ~600 family-specific lines ≈ 3.6k–4.8k, plus ~300 shared (done) | this session |
| finite labels, top-level composition, halting cleanup | 400–700 | item 1 + glue |
| D4 time bounds | +1.5k–2.5k | item 2, unmeasured (+40–60% guess) |
| D2 (`unaryBound`), link to verifier tables | 400–600 | unchanged / item 3 |
| **D total** | **≈ 7k–9.5k** | vs 4.0k–5.6k (D1 session) and 4k–9k (P6) |
| A + B + C | 3.9k–6.5k | unchanged (P6); C4/C8 overlap partly with the per-family spec/sortedness above |
| **Total** | **≈ 11k–16k lines** | vs 7.5k–12k (D1 session) and 8k–15k (P6) |

Plainly: the true cost is **substantially higher than last session's 7.5k–12k**, and at or
slightly above the top of P6's original 8k–15k. At ~900 verified lines per session, that is
**~13–18 more sessions** for Cook–Levin hardness alone. It still makes zero progress on
`sat_in_p`.

---

# FINITE LABELS + TIME BOUND ON THE D3Fam FAMILY (session of 2026-09-28)

Scope: measure the two costs left unmeasured last session, on the *existing* family. No new
family; CookLevin.lean and SatInP.lean untouched.

## Time-bound target (written BEFORE any bound was proved)

"Done" means this theorem, with no `sorry` and only the three standard axioms:

```
gen_time (T H : ℕ) (hwf : ∀ i < N, WF L la na wa H i) (o : List Bool) :
  ∃ (v : Bool) (S : ∀ k, List (GΓ k)),
    RunLe (prog L la na wa N) (genC L N * (T + H + 1) ^ 5)
      ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
    S .out = encodeCNF (family L la na wa T H N) ++ o
```

* `RunLe M B c d := ∃ n ≤ B, Run M n c d`. This is D1's exact-count `Run` with an upper bound,
  not `Reach`.
* `genC L N` is an explicit constant depending only on the layout constants `A, KK, g, d` and on
  `N`. It does not depend on `T`, `H` or the tables `la, na, wa`.
* Degree 5 is what this machine costs: `T` time steps × `N` clauses × `O(V²)` per clause (the gap
  emitter compares counters once per skipped slot), with `V = (T+1)·W` and `W = O(H)`. The degree
  was fixed from the machine before proving; it is not tuned to the proof.
* Also required: the `Polynomial ℕ` form, `genC L N * (T+H+1)^5 = (genPoly L N).eval (T + H)`,
  which is the shape `TM2ComputableInPolyTime` consumes. Comp.lean's `eval_mono` then gives
  monotonicity for free.
* Proof route: an intermediate explicit bound `genBound L N T H`, built from D1's exact
  per-primitive counts (`copy_run`, `mul_run`, `emitDiff_run`, `xferE_run`, `forLoop_*`), then
  `genBound ≤ genC · (T+H+1)^5` by pure arithmetic.

## Outcome: target met exactly as stated

`PvsNP.D3Fam.gen_time` is proved with the statement above, with
`genC L N := 323 · (A + KK + g + d + N + 1)^5` and `genPoly L N := C (genC L N) · (X+1)^5`.
`genPoly_eval : (genPoly L N).eval (T + H) = genC L N · (T+H+1)^5`. Axioms:
`[propext, Classical.choice, Quot.sound]`.

## Part 1: finite labels (built incrementally, checked after each change)

What changed:
* `GL` became `GL (N m : ℕ)`. Situation indices are `Fin N` and literal indices `Fin m`, with
  `m = L.nLits`.
* `CK, GK, MS, PS, LS, GL` all have `deriving DecidableEq, Fintype`. Mathlib already provides
  `Fintype Ordering`.
* **`genTM : FinTM2` typechecks**, with `K := GK`, `Λ := GL N L.nLits`, `σ := Bool`,
  `k₀ := .c .Tn` and `k₁ := .out`. So every finiteness field of Mathlib's `FinTM2` (`Fintype K`,
  `Fintype Λ`, `Fintype σ`, `Fintype (Γ k₀)`) is satisfied by the real generator program `prog`.

The explicit check requested: did anything relying on `decide`/`rfl` stop working?
* **Stack distinctness by `decide`: still works, unchanged.** The stack type `CK` did not change.
  Labels never appear in distinctness side conditions.
* **Program equations by `rfl`: still work everywhere.** This includes symbolic `i : Fin N` and
  `j : Fin L.nLits` (e.g. `prog (.lit i j (.r o)) = xfer …`). The pattern match is on
  constructors, and `Fin` values built as `⟨j, h⟩` are definitionally fine thanks to proof
  irrelevance.
* **What did break:** four gotos computed the next label by arithmetic (`.lit i (j-1)`,
  `.e00 (i-1)`, `.e00 (N-1)`, `.lit i (nLits-1)`). A `Fin` constructor needs a range proof there.
  * Fix: total helper gotos `GL.litL`, `GL.after`, `GL.sitL`, `GL.afterS`. They use `dite`, with
    an unreachable fallback `.done`/`.dtw`.
  * Two rewrite lemmas, `litL_of_lt` and `sitL_of_lt`, are used at the 6 proof sites that step
    through these gotos.
  * Result: **0 fix rounds** (it compiled on the first check), and the 8-instance `#eval` gives the
    same step counts and outputs as last session.
* **New capability checked (scratch probe, deleted):** kernel `decide` over the label type itself
  works for concrete `N`, e.g. `Fintype.card (GL 2 2) = 144` and `∀ l : GL 1 2, …`. It is not
  available for symbolic `N`. No proof currently needs it.
* **Not covered:** labels indexed by verifier-derived finite types (`Λ_V`, symbols). The mechanism
  is the same (a `Fintype` field), but it was not exercised. `genTM`'s input stack is the unary
  counter `Tn`, not the Bool-encoded instance, and at `done` it leaves non-empty counters. The
  real D-block machine needs an input decoder (D2) and a halting cleanup (unmeasured).

**Cost: +44 lines net** (899 → 943; diff +82/−38; +27 non-comment lines). Of those, ~30 are the
helper gotos + lemmas + `deriving` clauses + `genTM`, and ~15 are proof-site edits.
**Last session's guess was +150–250, so it was too high by ~4–5×.**

## Part 2: explicit polynomial time bound

Library (Prog.lean, kept, root): **+104 lines**, 0 fix rounds.
* `RunLe M B c d := ∃ n ≤ B, Run M n c d`, with `.mono/.trans/.refl/.reach` and `Run.le`.
* `Bud M K X c d := ∃ n, K + n ≤ X ∧ Run M n c d` with `Bud.start`, `Run.bud`, `RunLe.bud` and
  `Bud.fin`. This is goal-directed chaining with an accumulated cost `K`. Every implicit argument
  is fixed by first-order unification, so last session's `(prim …).reach.trans ?_` chains became
  `(prim …).bud ?_` with *no other change to the chain*. That is why threading bounds was cheap.
* `forLoop_le`: a uniform per-iteration bound `B` gives a total of `n (B+1) + n + 2`.

Reused, not reinvented: every per-primitive count comes from D1's exact `Run` lemmas (`copy_run`
2m+2, `mul_run` m(2n+3)+m+2, `emitDiff_run` gap(3q+6)+3q+4, `xferE_run`/`xfer_run` n+1).
Comp.lean's `eval_mono` applies at the D4 stage via `genPoly`; it was not needed here.

Family (D3Fam.lean): **+145 lines net** (943 → 1088; diff +214/−69; +109 non-comment lines).
Two fix rounds:
1. `simp` rewrote the product hints `kA·x ≤ KK·x` back into `kA ≤ KK`.
2. `rw [Nat.succ_mul]` matched the literal `3 * p` as `(2+1) * p`.

Breakdown:
* ~25 lines: bound definitions `litE`, `clauseB`, `bodyB`, `preB`, `genBound`.
* ~60 lines: conversions and arithmetic closers in `lit_run`/`lits_run`/`clause_run`/`sits_run`/
  `time_body`/precompute. Each closer is simp + 1–3 product hints + `omega`, or `ring_nf; omega`.
* 59 lines: the polynomial collapse (`section Poly`).
  * `genBound_mono` (`gcongr`), then substitute `Layout.uni k` (all constants `k`) and
    `T = H = y`, which gives a concrete 2-variable polynomial.
  * `genBound_uni`: `nlinarith` with the 19 monomial facts `k^a y^b ≤ k^5 y^5`. The monomial list
    and the coefficient sum 323 were computed with sympy (evidence only; Lean re-proves it).

**Relative cost: +145 family lines = +16% of the 899-line family, or ~+24% of its ~600
family-specific lines, plus the one-time +104 library. Last session's guess was +40–60% per
family, so it was too high by roughly 2×.**

Sanity (evidence, not proof): the `#eval` of the finite-label machine on the same 8 instances
returns `steps ≤ genBound` on all of them.

| instance | steps | `genBound` | `genC·(T+H+1)^5` |
|---|---|---|---|
| ⟨2,2,2,1⟩ N=2 T=2 H=2 | 5127 | 16147 | 1.0·10^11 |
| ⟨3,2,3,2⟩ N=3 T=2 H=3 | 28718 | 92951 | 1.4·10^12 |
| ⟨1,1,1,1⟩ N=1 T=1 H=1 | 150 | 323 | 6.1·10^8 |
| ⟨2,3,2,2⟩ N=2 T=3 H=2 | 23318 | 80534 | 6.2·10^11 |
| KK=0 | 523 | 1265 | 1.1·10^10 |
| d=0 | 2001 | 6027 | 2.0·10^10 |
| N=0 | 129 | 195 | 1.1·10^10 |
| T=0 | 59 | 59 | 1.0·10^9 |

The explicit `genBound` is within ~3.5× of the real count. The collapsed monomial form is loose by
up to 10^8, which is irrelevant for polynomial time.

## What carries forward into the real D3 files vs. what stays scratch

**Carry forward:**
* Prog.lean `RunLe`/`Bud`/`forLoop_le` (already library).
* The `Fin`-indexed label pattern: `inductive GL (N m)` + `deriving DecidableEq, Fintype`, the
  total `dite` goto helpers with `_of_lt` lemmas, and a `genTM : FinTM2` typecheck as a standing
  finiteness test.
* The `.bud` chain style with arithmetic closers.
* Per-level bounds, with uniform bounds through `forLoop_le`.
* The collapse technique: `gcongr` monotonicity → uniform-constant layout → monomial facts →
  `nlinarith`, and the `Polynomial ℕ` wrapper.
* Also, as before: `gapEnc`/`Inc`/`encodeClause_denseClause`/`gapEnc_shift`/`inc_of_mono`, the
  `st` view, and the `lit_run` design.

**Scratch (to be superseded):**
* The draft C3 layout (`Layout`, `litPos`, `kA`/`kB`/`cst`).
* The abstract tables `la, na, wa`.
* The specific bound constants (`litE … preB`, 323), which are machine-specific.
* `genTM`'s unary input on `Tn` and its non-clean halt.
* `gen_correct` (now a redundant corollary of `gen_run`).

D3Fam.lean remains **not a root**.

## Updated P6 / D-block estimate (supersedes 2026-09-27's 7k–9.5k D, 11k–16k total)

| Block | Estimate | Basis |
|---|---|---|
| D1 library | 958 (done) | measured (854 + 104) |
| D3 families | 6–8 × ~600 family-specific ≈ 3.6k–4.8k, + ~300 shared (done) | unchanged (last session's measurement) |
| finite labels + top-level composition + halting cleanup + input decoding | 250–500 | finite labels **measured** at ~45 per generator (was 150–250); the rest unmeasured |
| time bounds | 6–8 × 150–250 ≈ 0.9k–2.0k | **measured** 145 for a family with no runtime inner loop; upper end allows nested-loop families |
| D4 glue (T, H ↔ input length, `Polynomial` composition) | 200–400 | new line; previously folded into "D4 +1.5k–2.5k" |
| D2 (`unaryBound`), link to verifier tables | 400–600 | unchanged |
| **D total** | **≈ 6.6k–9.6k** | vs 7k–9.5k |
| A + B + C | 3.9k–6.5k | unchanged, unmeasured |
| **Total** | **≈ 10.5k–16k lines** | vs 11k–16k |

Both measured costs were **lower** than guessed (finite labels ~4–5× lower, time bounds ~2×
lower), but the estimate barely moves. Together they were ~2k of a 7k–9.5k block. The block is
dominated by the per-family content (~600 lines × 6–8, measured once) and the unmeasured
A/B/C blocks. At ~900 verified lines per session: **~12–17 more sessions** for Cook–Levin hardness
alone. None of this touches `sat_in_p`; status stays **NOT PROVED**.

Largest remaining unmeasured risks, in order:
1. families with runtime inner loops (cell one-hot over `j < H`, shifts by `δ`);
2. the input decoder and a clean halt meeting `TM2OutputsInTime`'s final-configuration shape;
3. blocks B/C (C6 soundness).

---

# INNER-LOOP FAMILY: CELL ONE-HOT (session of 2026-09-28, second)

## Lakefile (approved)

Diff applied (shown before applying):
```
-roots = ["Challenge", "Comp", "CookLevin", "SatInP", "Solution", "Prog"]
+roots = ["Challenge", "Comp", "CookLevin", "SatInP", "Solution", "Prog", "D3Fam"]
```
`lake build` → `✔ [1260/1261] Built D3Fam (101s)`, `Build completed successfully (1261 jobs).`
Only warnings: the three known `declaration uses 'sorry'` (Challenge.lean:3, CookLevin.lean:803,
SatInP.lean:15). D3Fam itself builds with no warnings.

## Choice of family (written before any code)

**Caveat first.** CookLevin.lean has no clause families yet: it has only the dense *encoding*
(`encodeClause`/`encodeCNF`). The families exist only as the P2 list in this file (C4 is not written).
So "the real CNF encoding" here means the P2 family rendered through the real `encodeCNF`. Also,
P4 does not rank one-hot against shifts; the ranking below is mine.

**Chosen: the cell one-hot family** (P2, "one-hot: (T+1)·K·H·(1+g²)" part). For every time
`t ≤ T`, stack `k < KK`, depth `j < H`, with base `B = cIdx H t k j 0`:
* at-least-one: `⋁_{x<g} C[t,k,j,x]`;
* at-most-one: `¬C[t,k,j,x] ∨ ¬C[t,k,j,y]` for all `x < y < g`, ordered by `y`, then `x`.

Why this one rather than the cell-shift family:
* It has the loop structure asked for: **two runtime loops, one over time (`T+1`) and one over
  height (`H`)**, nested, plus a loop over stacks. The cell base is computed from the three loop
  counters at run time.
* It is the cheaper representative. The shift family has the same loop nest, plus a
  situation-dependent offset `j − δ` with boundary cases (`j < |pushed|`, `j − δ ≥ H`) and
  subtraction in the index arithmetic. Those are extra per-family index arithmetic, not a
  different loop structure. **So this measurement is a lower bound for the shift family.**
* Per cell it needs a 2-D label chain (pairs `x < y`), which the first family did not have.

## Machine design (before code)

* The loops over `t` (`T+1` iterations), `k` (`KK` iterations) and `j` (`H` iterations) are all
  **runtime `forHead` loops** on counters, nested three deep. `k` is also a runtime loop (its
  counter is preloaded with `KK`), so labels carry no `k`/`j`/`t`.
* Per `k`: `KB := t·W + A + k·(H·g)`. Per `j`: `CB := KB + j·g` (= `cIdx H t k j 0`).
* Per cell, a label chain over clause kinds `CL g = alo | amo (x y : Fin g)`, generated last-first,
  since everything is prepended. Per clause: the terminator, `P := V`, then the literals last-first.
  Each literal is `Q := CB + off`, the gap loop, the slot, then drain `Q`.
* Labels are finite from the start: `GL g` with `CL g` and `Fin g` fields, `deriving Fintype`.
* Spec (`ohFamily L T H : CNF`) is stated over `ℕ`, independent of labels:
  `(range (T+1)).flatMap t, (range KK).flatMap k, (range H).flatMap j, cellCNF g V (cIdx H t k j 0)`.

## Time-bound target (written BEFORE any bound is proved)

```
oh_time (T H : ℕ) (o : List Bool) :
  ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
    RunLe (prog L) (ohC L * (T + H + 1) ^ 6)
      ⟨some (.pre .inc), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
    S .out = encodeCNF (ohFamily L T H) ++ o
```
* **Degree 6 in `T+H+1`, fixed now from the machine.** There are `(T+1)·KK·H` cells and
  `1 + g(g−1)/2` clauses per cell. Each clause costs `O(V²)` (the gap loop compares counters once per
  skipped slot, `V = (T+1)·W`, `W = A + KK·H·g`). So the cost is `(T+1)·H·V² = O((T+1)³H³)`, one
  degree more than the first family's `T·N·V²` (degree 5), because the extra `H` factor is now a
  runtime loop instead of a constant `N`.
* `ohC L` depends only on the layout constants `A, KK, g` (not on `T`, `H`). Its exact
  exponent and coefficient come out of the monomial collapse, as in the first family. No
  hypotheses: this family has no tables, so there is no `WF`.
* The proof route is the same as the first family: an explicit `ohBound`, built from the D1
  per-primitive counts, then `ohBound ≤ ohC·(T+H+1)^6` by `gcongr` + uniform constants + `nlinarith`.

## Outcome: target met as stated

`PvsNP.D3OH.oh_time` is proved with the statement above, with
`ohC L := 668 · (A + KK + g + 1)^7` (degree 7 in the layout constant, **degree 6 in `T+H+1`, as
fixed beforehand**) and `ohPoly L := C (ohC L) · (X+1)^6`, `ohPoly_eval`. No `sorry`. The file was
checked with `lake env lean D3OneHot.lean`: no errors, no warnings, 3m16s, of which ~2 min is one
`nlinarith` (see below).

`#print axioms` on **all 92 declarations** of D3OneHot.lean (a scratch copy with generated
`#print axioms` lines): 24 × `[propext, Classical.choice, Quot.sound]`, 20 × `[propext, Quot.sound]`,
6 × `[propext]`, 42 × none. No `sorryAx`. Key lines, quoted:
`'PvsNP.D3OH.oh_time' depends on axioms: [propext, Classical.choice, Quot.sound]`,
and the same for `oh_run`, `stLoop`, `rows_run`, `cell_run`, `kbody_run`, `tbody_run`, `ohBound_le`.

Banned-token scan (`sorry|admit|axiom|native_decide|decide +native|implemented_by|@[extern|unsafe|
partial|open private|set_option debug|run_cmd|addDecl`) on the Lean/lake files touched,
D3OneHot.lean and lakefile.toml: no matches. D3Fam.lean, Prog.lean and CookLevin.lean were not
touched this session. Final `lake build`: `Build completed successfully (1261 jobs)`, with only the
three known `sorry` warnings.

**Evidence (not proof).** `#eval` of the real machine on 8 instances, including `g=0`, `KK=0`,
`H=0` and `T=0`. In all 8, the last label before halting is `done`, and the output equals
`encodeCNF (ohFamily …)`. (My first version of the halt check this session was buggy: it looked at
the post-halt config. The version quoted here checks the label before the halt.)

| Layout ⟨A,KK,g,d⟩, T, H | steps to `done` | `ohBound` | `ohC·(T+H+1)^6` | bits |
|---|---|---|---|---|
| ⟨1,1,2,0⟩ 1 1 | 489 | 2792 | 3.8·10^10 | 56 |
| ⟨2,2,3,1⟩ 2 2 | 67285 | 778183 | 2.2·10^13 | 4128 |
| ⟨1,2,4,0⟩ 1 2 | 56199 | 631662 | 5.7·10^12 | 3920 |
| ⟨0,1,1,0⟩ 0 1 | 69 | 135 | 9.3·10^7 | 4 |
| ⟨1,1,0,0⟩ 1 2 (g=0) | 176 | 326 | 6.0·10^9 | 24 |
| ⟨1,0,2,0⟩ 2 2 (KK=0) | 88 | 112 | 1.7·10^11 | 0 |
| ⟨1,2,2,0⟩ 2 0 (H=0) | 176 | 266 | 1.4·10^11 | 0 |
| ⟨2,1,3,0⟩ 0 3 (T=0) | 2587 | 21113 | 2.3·10^12 | 288 |

## Line counts (D3OneHot.lean, 1005 lines total)

| Part | Lines | What |
|---|---|---|
| header / imports / doc | 24 | — |
| **reusable library** | **209** | The `[LIB]` section (201 lines): the generic counter view `SK C`/`SΓ C`/`st` plus update lemmas; the wrappers `emitS`, `emitOut`, `incS`, `drainS`, `xferES`, `copyS`, `mulS`/`mulS_run`, `gapS`, each restating a Prog.lean primitive in the `st f o` view; `bud_st` (transport along an equality of counter functions); **`stLoop`** (a runtime `for` loop in the counter view, 50 lines). Plus `Inc.mono_lo` (8 lines). |
| **family-specific correctness** | **≈ 626** | spec (23), machine + labels + goto helpers (≈ 160), literal positions/sortedness (≈ 60), `lit_run`/`lits_run`/`clause_run` (≈ 110), the 2-D clause chain `row_run`/`rows_run` (≈ 70), the cell/k/t loop bodies + `base_le`/`kb_le` + precompute + `oh_run` (≈ 200) |
| **time bound** | **≈ 146** | bound definitions `litE … ohBound` (20), cost closers inside the run proofs (≈ 35), bound expressions in statements (≈ 10), `section Poly` (81, of which 34 lines are the `nlinarith` monomial list, one per line) |

Fix rounds: 5.
1. `forLoop_le` needed explicit stack arguments.
2. `CL.WF` was not unfolded, and a lemma for lowering `Inc`'s lower bound was missing.
3. Field notation failed on an aliased namespace.
4. Three small closers: `flatMap_map`, `c ≤ 2c`, and a final `rfl`.
5. A multi-line `by` inside parentheses.

## Comparison with the first family (the question for this session)

| Measure | 1st family (D3Fam, no runtime inner loop) | 2nd family (cell one-hot, runtime `t`/`k`/`j` loops) |
|---|---|---|
| family-specific correctness | ≈ 600 | **≈ 626 (+4%)** |
| time bound, per family | 145 (+16% of the file, ≈ +24% of family lines) | **≈ 146 (≈ +23% of family lines)** |
| new reusable library | ≈ 300 (then) + 104 (`RunLe`/`Bud`) | 209 (counter view + `stLoop`) |
| polynomial degree in `T+H+1` | 5 | 6 |
| `nlinarith` collapse | 19 monomials | 34 monomials, **~2 min elaboration** |

**Plainly: this family is not measurably more expensive per family (+4% correctness, the same
~+23% bound overhead).** But the comparison flatters it, for three reasons:
1. It paid a one-time **209-line library** first. Without `stLoop` and the `st` wrappers, each loop
   level would have cost about what the first family's time loop did (~70 lines with its
   invariant), and every primitive use would have needed the `rw [update_st_c]` bookkeeping. My
   estimate is that without the library this family would be ≈ 800–850 family lines. The library
   is paid once, not per family.
2. Its index arithmetic is easier. It uses only `+` and `·` (`base = j·g + k·H·g + t·W + A`), with
   no `/`, no `%` and no tables, so there is no `WF` hypothesis at all. Sortedness cost ≈ 60 lines
   here, against 120 in the first family.
3. **It is the cheaper representative.** The cell-shift family keeps this loop nest and adds a
   situation-dependent offset `j − δ` with boundary cases. That is unmeasured and will cost more.

## New proof techniques needed (vs the first family)

* **Nested runtime loops: one new library lemma, no new invariant technique.** `stLoop` wraps
  `forLoop_le` with a fixed discipline: the body restores every counter and only prepends output.
  So the loop invariant is written once: output = `(range' (n-i) i).flatMap blk ++ o`, and every
  counter other than the loop's own pair is unchanged. Each loop level then costs ≈ 15 lines to
  instantiate. Nesting needed nothing special: the inner loop's invariant may mention the outer
  loop's counters, because `forLoop_le` only forbids its *own* pair.
* **`bud_st` + `funext x; cases x <;> simp`** replaced syntactic `rw` of nested `update` terms
  after `copyS`/`mulS_run`. This is new, and it is the main reason the chains stayed short.
* **A 2-D label chain** (the pairs `x < y`): two nested inductions over label parameters (`row_run`
  inside `rows_run`). The goto helpers `pr`, `yDone` and `nextC` use the same `dite` style as
  before. The chain's cost bound `(1 + y²)·clauseB` needed one `nlinarith` (a quadratic in the chain
  index).
* **Index arithmetic: nothing beyond the known patterns.** `base_le`/`kb_le` use
  `← Nat.succ_mul` + `omega`, and `base_eq` uses `ring`. No `/` or `%`.
* **New cost risk: the collapse step.** At degree 6 × 7, `nlinarith` with 34 monomial hints takes
  ~2 minutes, while the rest of the file takes ~70 s. A family with more monomials may need the
  collapse split into per-level lemmas (bounding each `…B` definition separately), which would add
  lines.

## Updated P6 / D-block estimate (supersedes the 2026-09-28 morning table)

| Block | Estimate | Basis |
|---|---|---|
| D1 library | 958 (done) + 209 (counter view and `stLoop`; done, to be migrated) ≈ 1.17k | measured |
| D3 families | 6–8 families. Cheap ones (label one-hot, idle, accept): ~450–600. The two measured ones: ~600–630. **Shift family: ~800–1000 (boundary cases; unmeasured).** Total **≈ 3.7k–5.2k** | two measurements; the upper end is **raised** for the shift family, not averaged away |
| time bounds | 6–8 × 150–250 ≈ 0.9k–2.0k | **measured twice**, ≈145 each; the upper end is kept because of the collapse-scaling risk |
| finite labels + top-level composition + halting cleanup + input decoding | 250–500 | finite labels cost ~0 extra this time (built in from the start); the rest is unmeasured |
| D4 glue | 200–400 | unchanged |
| D2 (`unaryBound`), link to verifier tables | 400–600 | unchanged |
| **D total** | **≈ 6.6k–9.9k** | vs 6.6k–9.6k |
| A + B + C | 3.9k–6.5k | unchanged, unmeasured |
| **Total** | **≈ 10.5k–16.4k lines** | vs 10.5k–16k |

The second data point confirms ~600 family lines for a family with runtime inner loops, once the
counter-view library exists. The estimate barely moves. The largest remaining D-block uncertainty
is now the **shift family**, not loop nesting. At ~900 verified lines per session, that is
**~12–17 more sessions** for Cook–Levin hardness alone. None of this touches `sat_in_p`; status
stays **NOT PROVED**.

## What carries forward vs. what is scratch

**Carry forward** (to migrate into Prog.lean or a `CntView.lean` when the real D3 files start):
* the whole `[LIB]` section: `SK`/`SΓ`/`st`, the wrappers `emitS … gapS`, `bud_st`, `st_eta`,
  **`stLoop`**, plus `Inc.mono_lo`;
* the clause-kind pattern `clits`/`bnd`/`inc_drop`/`lits_run`/`clause_run`. It is parametric in an
  offset function (`CL.off`, `CL.nl`, `CL.sg`), so it fits any family whose clause literals are
  `base + small offsets`;
* the machine layout pattern: runtime loops over preloaded counters, each body restoring every
  counter, with the cell base computed incrementally per loop level (`KB` per `k`, `CB` per `j`);
* the 2-D label chain pattern (`pr`/`yDone`/`nextC`, with `row_run` inside `rows_run`);
* the collapse technique, now with the known scaling caveat.

**Scratch** (to be superseded):
* D3OneHot.lean as a file (exploratory, **not a root**, imports D3Fam);
* its `CK` counter set and `GL g` labels (the real generator will merge all families into one
  machine);
* D3Fam's draft C3 layout, which this file reuses (`Layout`, `rowW`, `numVars`, `cIdx`);
* the bound constants (`litE … ohBound`, 668, exponent 7);
* the unary input on `Tn`/`Hs` and the non-clean halt (counters left non-empty at `done`). Both
  were out of scope this session, as instructed.

D3Fam.lean is now a lakefile root (approved), but it stays **exploratory**. Being a root only
means that `lake build` checks it and that other files can import it.

---

# CELL-SHIFT FAMILY (session of 2026-09-28, third) — plan written BEFORE any code

## Lakefile

Not changed this session. The approved-in-principle change (add `D3OneHot` to the roots) is
printed as a diff at the end of the session report and **not applied**, per the new process rule.
Consequence for this session: `D3Shift.lean` imports `D3OneHot` (for the [LIB] counter view), and
is checked by compiling `D3OneHot.olean` into the session scratchpad and prepending that directory
to `LEAN_PATH`. Nothing under `.lake/` or the lakefile is touched.

## Design decision forced before code: situation variables (a finding in itself)

The literal form in P3, `situation(t) ∧ C[t,k,j−δ,x] → C[t+1,k,j,x]`, expands the situation into
its label literal plus all `KK·d` window literals. Rendered as a *dense* clause this breaks the
generator's sortedness requirement: the source literal `C[t,k,s,x]` lies at stack `k`'s depth `s`,
which sits **between** the window literals of stack `k` (depths `< d`) and those of stack `k+1`,
and **coincides** with a window cell when `s < d`. Emitting it in position order would need a
sorted insertion whose index depends on `(k, s)`, at run time (`s = u + c` is a loop counter).
This is the top-indexed model's first awkward boundary case, and it is in the clause *shape*, not
the index arithmetic.

**Fix (standard Tseitin step): one situation variable `S[t,i]` per time step and situation**,
placed in the label/state block of row `t` (position `t·W + sa i`, `sa i < A`). Then
* shift clauses have 3 literals, `¬S[t,i] ∨ ¬C[t,k,u+c,x] ∨ C[t+1,k,u+p,x]`, automatically sorted
  (`S` in the `A` block < row-`t` cell < row-`t+1` cell);
* the definition clauses `¬X[t,la i] ∨ ⋁ ¬C[t,k',j',wa i k' j'] ∨ S[t,i]` are **exactly the D3Fam
  family** with `na i` replaced by `sa i` and the head in row `t` instead of `t+1` (not built here).
* Soundness only needs the direction situation ⇒ `S[t,i]`: spurious `S[t,i]=true` only *adds*
  constraints; completeness sets `S[t,i] :=` "situation `i` holds at `t`".
* Cost in the P2 accounting: `A` grows by `N` (a constant), clause count drops (the long
  situation part is emitted once per `(t,i)` instead of once per `(t,i,k,j,x)`).

## The exact clause family (`shFamily`)

Parameters: layout `L = ⟨A, KK, g, d⟩` (as in D3Fam; symbol code `0` is ⊥), `N` situations, and
verifier tables `sa i` (situation variable offset), `pl i k`, `cn i k`. Per the sharpened B1
(P7): `pl i k = |P k|` = symbols pushed this step and still on top; `cn i k = j k` = **net
original symbols consumed** (not the raw pop count). `d` must bound both `cn` and `pl` (so the
real `d` is `max(deepest read, pushes still on top)`; enlarging the window is harmless).
Write `p = pl i k`, `c = cn i k`, `m = max p c`, `V = numVars T H`, `s = xIdx H t (sa i)`.

For `t < T`, `i < N`, `k < KK` (in that order), the block `shBlk t i k` is
1. **in-range shifts**: for `u < H − m`, then `x < g`:
   `¬S[t,i] ∨ ¬C[t, k, u + c, x] ∨ C[t+1, k, u + p, x]`
   (target depth `j = u + p ≥ p`; source depth `j − p + c = u + c`, the `j − δ` of P3 with
   `δ = p − c`);
2. **overflow fill** (only when `c > p`): for `r < c − p`:
   `¬S[t,i] ∨ C[t+1, k, H − c + p + r, 0]` (target depths `[H−(c−p), H)` whose source
   `≥ H` is beyond the cap; they must be ⊥).

## Boundary cases (the `j − δ` offset), and how each is handled

| case | target depths `j` | handling |
|---|---|---|
| pushed region `j < p` | `[0, p)` | **not in this family**: the pushed-fill family (`¬S ∨ C[t+1,k,j,P_j]`, constant-size per `(t,i,k)`) |
| source in window, `j−p+c < d` | part of `[p, …)` | in the family; clause redundant given `S[t,i]`'s definition but harmless; no special case needed *thanks to the S variables* |
| in range, `c ≤ p` (net push) | `[p, H)`, source `[c, H−p+c)` | runtime loop over `u < H − p`; source cells `[H−p+c, H)` are dropped (they are ⊥ under the height precondition) |
| in range, `c > p` (net pop) | `[p, H−c+p)` | runtime loop over `u < H − c` |
| overflow, `c > p` | `[H−c+p, H)` | runtime loop over `r < c − p` with position `(U + r)` where `U = H − c` |
| `H < m` | — | excluded by `WF` (`d ≤ H`) |
| `g = 0` | — | excluded by `WF` (`0 < g`: ⊥ must have a code) |

## Loop nest (machine)

* `t < T`: runtime `stLoop` (`TW := t·W` per step).
* `i < N`, `k < KK`: **label chains** (`Fin N`, `Fin KK` in the labels), because `p, c, sa i` are
  table values that must be hard-wired constants per label.
* per `(i,k)`: `KB := TW + A + k·HG`; `U := H − m` (copy `Hs`, then a label chain of `m ≤ d`
  decrements, `Fin (d+1)`); `R := c − p` (emit constant).
* overflow loop: runtime `stLoop` over `R`; body `CB := KB + (U + r)·g`, `CW := CB + W`, one
  2-literal clause.
* in-range loop: runtime `stLoop` over `U` (value `u`); body `CB := KB + u·g`, `CW := CB + W`, then a
  label chain over `x : Fin g`, one 3-literal clause each.
* literals: `Q := base + const` with `base ∈ {TW, CB, CW}` (a per-literal base counter; new relative
  to the one-hot family, which had one base).
* Output order: everything is prepended, so the machine does overflow before in-range and runs
  label chains downward.

## Time-bound target (fixed now, before proof)

```
sh_time (T H) (hwf : WF L sa pl cn N H) (o) :
  ∃ v S, RunLe (prog L sa pl cn N) (shC L N * (T + H + 1) ^ 6)
           ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
         S .out = encodeCNF (shFamily L sa pl cn N T H) ++ o
```
Degree 6: `T · N·KK · (H·g + d) clauses · O(V²)` with `V = O(T·H)`. `shC L N` depends only on
`A, KK, g, d, N`. The collapse will be split per level from the start if one `nlinarith` exceeds
about 1 minute.

## Outcome: target met as stated

`PvsNP.D3SH.sh_time` is proved with exactly the statement fixed above, with
`shC L N := 591 · (A + KK + g + d + N + 1)^7` (degree 6 in `T+H+1`, as fixed beforehand) and
`shPoly L N := C (shC L N) · (X+1)^6`, `shPoly_eval`. Intermediate: `sh_run` with the explicit
`shBound L N T H`. No `sorry`.

Checks (all run this session, output quoted):
* `lake env lean D3Shift.lean` (with `LEAN_PATH` prefixed by the scratch dir holding
  `D3OneHot.olean`): `exit=0`, no errors, no warnings, ~95–100 s.
* `#print axioms` on **all 98 declarations** (scratch copy with generated lines): 22 ×
  `[propext, Classical.choice, Quot.sound]`, 21 × `[propext, Quot.sound]`, 4 × `[propext]`, 51 ×
  none. No `sorryAx`. E.g. `'PvsNP.D3SH.sh_time' depends on axioms: [propext, Classical.choice,
  Quot.sound]`, and the same for `sh_run`, `ik_run`, `sbody_run`, `obody_run`, `sb_run`, `xs_run`,
  `shBound_le`.
* Banned-token scan (`sorry|admit|axiom|native_decide|decide +native|implemented_by|@[extern|unsafe|
  partial|open private|set_option debug|run_cmd|addDecl`) on D3Shift.lean and lakefile.toml: no
  matches. No other Lean file was edited (D3OneHot.lean, D3Fam.lean, Prog.lean unchanged).
* `lake build`: `Build completed successfully (1261 jobs).`, only the three known `sorry` warnings
  (Challenge.lean:3, CookLevin.lean:803, SatInP.lean:15). D3Shift is not a root, so this does not
  check it; the `lake env lean` run above does.

**Evidence (not proof).** `#eval` of the real machine on 10 instances. The tables cover
`c > p`, `c < p`, `c = p`, `m = 0`, `H = m` (no in-range rows, overflow only), `g = 1`,
`KK = 0`, `N = 0`, `T = 0`. In all 10: last label `done`; output `= encodeCNF (shFamily …)`;
steps `≤ shBound`.

| ⟨A,KK,g,d⟩, N, T, H | steps | `shBound` | `shC·(T+H+1)^6` | bits |
|---|---|---|---|---|
| ⟨3,2,2,2⟩ 3 2 3 | 107341 | 731914 | 1.7·10^15 | 3864 |
| ⟨3,2,2,2⟩ 3 1 2 | 6632 | 81173 | 1.5·10^14 | 414 |
| ⟨3,2,1,2⟩ 3 2 4 (g=1) | 56101 | 327494 | 2.5·10^15 | 2448 |
| ⟨2,2,3,2⟩ 2 2 2 | 49924 | 428518 | 3.3·10^14 | 1892 |
| ⟨1,1,2,1⟩ 1 2 3, p=0 c=1 | 7178 | 29175 | 2.3·10^13 | 440 |
| ⟨1,1,2,1⟩ 1 2 3, p=1 c=0 | 5677 | 29175 | 2.3·10^13 | 352 |
| KK=0 | 87 | 180 | 5.4·10^14 | 0 |
| N=0 | 229 | 646 | 2.8·10^14 | 0 |
| T=0 | 102 | 102 | 1.5·10^14 | 0 |
| ⟨1,1,1,2⟩ 1 1 2, p=0 c=2 (H = m) | 341 | 1662 | 2.0·10^12 | 28 |

## Line counts (D3Shift.lean, 1206 lines) vs. the one-hot family

| Part | This family | One-hot | Change |
|---|---|---|---|
| **family-specific correctness** | **≈ 990** | ≈ 626 | **+58% (+≈365)** |
| **time bound** (cost defs 27, closers ≈ 55, bound terms in statements ≈ 10, `section Poly` 85) | **≈ 177** | ≈ 146 | +21% |
| **new reusable library** | 10 (`decS`) | 209 (one-time) | reused the 209 unchanged |
| header / doc | 29 | 24 | |

Family-specific breakdown: spec + `WF` 37; machine + labels 257 (vs ≈ 160); literal positions
(`clits`/`Mono`/`bnd`, now for an arbitrary position function) 47; literal/clause runs ≈ 135;
clause instances + `x` chain + decrement chain ≈ 140; the two loop bodies ≈ 130; the `(i,k)` block,
the `k`/`i` chains, time body, top ≈ 245.

**Plainly: this family is more expensive, by ≈ 58% in family lines and ≈ 21% in bound lines.**
Where the extra ≈ 365 lines went:
* ≈ 160 lines are the **boundary cases** themselves: the overflow clause (`ovPos`, `ovPos_mono`,
  `clits_ov`, `oBodyB`, `obody_run`), `U := H − m` (the decrement chain `sb_run` and its labels), and
  the extra loop setup in `ik_run`.
* ≈ 100 lines are the machine: two runtime loops per block instead of one, per-literal base
  counters, and a label type that had to be split into sub-inductives (below).
* The rest comes from two label chains (`i`, `k`) instead of runtime loops. They are needed because `p`, `c`, `sa i` are
  table values hard-wired per label.

Fix rounds: 12 (vs 5).
1. `deriving Fintype` failed on the flat 45-constructor label type.
2. A structural-recursion shape.
3. Implicit tables not pinned (2×).
4. `if 0+1=0` not reduced after `subst`.
5. `(t+1).succ` vs `t+1+1` atoms in `omega`.
6. `Fin` coercion blocked a `rw`.
7. `set`-variables in `simp`.
8. `(r+(H−c))·g` vs `(H−c+r)·g` atoms.
9. A `v` flag not threaded through `stLoop`.
10. A placeholder that could not be synthesized.
11. A missing `k < KK` fact.
12. A line-break syntax slip.

None was mathematical.

## `nlinarith`-style steps: none over a minute; the collapse got much cheaper

* The collapse `shBound_uni` (30 monomials, `k^7 y^6`) is proved by **plain `linarith`** with the
  monomial hints, not `nlinarith`. Profiled (`set_option profiler true`, scratch copy):
  `linarith took 1.82s`, `ring took 1.29s`.
* The same swap on the one-hot collapse (scratch copy of D3OneHot, `nlinarith` → `linarith`, not
  applied to the real file): `linarith took 998ms`, `ring took 935ms`, whole file checked in 71 s
  (`exit=0`), against 3m16s with `nlinarith` last session.
* Reason: `linarith` already multiplies out polynomial atoms. `nlinarith` also adds all pairwise
  products of the 34 hints (~600 extra atoms), which the certificate does not need.
* **The collapse-scaling risk flagged last session is resolved**: no split was needed. No other step
  in the file is slow; the whole file takes ~95–100 s, most of it import loading and `omega`.

## Boundary cases: what the top-indexed shift model handled awkwardly (the P5 risk)

No mismatch between the model and the generator was found: every proof went through, and the
`#eval` evidence agrees. But four things needed a design change or a new lemma:

1. **Design change (real): situation variables `S[t,i]`.** The literal P3 clause cannot be
   emitted as a sorted dense clause: its source literal `C[t,k,u+c,x]` interleaves with, or
   coincides with, the situation's window literals. The Tseitin fix adds `N` variables per row and a
   *definition family*, `¬X[t,la i] ∨ ⋁¬C[window] ∨ S[t,i]`, which is D3Fam's family with the head
   moved to row `t`. **Consequences for C:**
   * C3's layout gains the `S` block.
   * C4 gains the definition family.
   * C5 (completeness) must set `S[t,i] :=` "situation `i` holds at `t`".
   * C6 (soundness) uses only the direction "window ⇒ `S`", so a spurious `S = true` only adds
     constraints. That direction must be argued.
   * Not built: the definition family and the pushed-fill family (`j < p`).
2. **New case: the overflow region (net pop, `c > p`).** Target depths `[H−(c−p), H)` have their
   source above the cap. They need explicit ⊥ clauses, which are *correct only under the height
   precondition* (heights `≤ H − d` at `t` and `t+1`). The P2 choice `H = m + c·T + d + 1` provides
   that, but C5 must carry it. [**2026-09-30 correction:** the old formula did not provide this when `depth M > pushBound M`; P2 now uses `H = m + (T+1)·d + 1`, and `Sit.capH_height` proves the height precondition for it. See "H CORRECTION + DEPTH_COVER ASSEMBLY".] The dropped sources in the net-push case (`[H−p+c, H)`) need nothing.
   Coverage of target depths is exact, `p + (H − m) + (c − p)⁺ = H` with `m = max p c` (arithmetic
   check, not yet a Lean lemma). C2/C5 will need it.
3. **New primitive: a constant subtraction at run time** (`U := H − m`, `m ≤ d`). D1 has no subtract
   primitive, so it became a `Fin (d+1)`-indexed decrement chain (`sb_run`, ≈ 25 lines, plus the
   `[LIB]` wrapper `decS`). Using `m = max p c` as the loop bound handles both signs of `δ = p − c`
   with **no runtime branch**. The overflow then reuses `U = H − c`, with position `(U + r)·g`.
4. **B1 wording, again:** the shift family also needs `p = |P k| ≤ d` (for `m ≤ d ≤ H` and the finite
   decrement labels). B1/P7 said `d` bounds the net consumption and the read depth. **`d` must also bound
   the pushes still on top**, i.e. `d := max(deepest read, max |P k|)`. Enlarging the window is
   harmless (more situations, still a constant).

Also a Lean-engineering finding: **`deriving Fintype` gives up on a flat label inductive with ~45
constructors carrying `Fin`/`Bool`/`MS` fields**. Splitting it into sub-inductives (`ST`, `BD g`,
nested under `GL.s i k` / `GL.b i k`) fixed it, with no proof cost. The merged real generator will
need this structure from the start.

## Updated P6 / D-block estimate (supersedes the second 2026-09-28 table)

| Block | Estimate | Basis |
|---|---|---|
| D1 library | ≈ 1.18k (958 + 209 + 10) | measured |
| D3 families, measured | 600 + 626 + 990 ≈ 2.2k | three measurements |
| D3 families, remaining (situation definition ≈ D3Fam variant; pushed fill; label/state one-hot; halted-idle; accept; init) | 5 × 350–700 ≈ 1.8k–3.5k | the S-definition family largely reuses D3Fam; fill/idle resemble the shift family's overflow part |
| time bounds | 145 / 146 / 177 measured; remaining 5 × 150–200 → total ≈ 1.2k–1.5k | the collapse-cost risk is gone (`linarith`) |
| finite labels + top-level composition + halting cleanup + input decoding | 300–600 | +100 at the top end: the label type must be split into sub-inductives |
| D4 glue | 200–400 | unchanged |
| D2 (`unaryBound`), link to verifier tables | 400–600 | unchanged |
| **D total** | **≈ 7.3k–10.0k** | vs 6.6k–9.9k |
| A + B + C | 4.1k–7.0k | +0.2k–0.5k for the `S` variables (C3/C4/C5/C6) and the overflow-coverage lemma |
| **Total** | **≈ 11.4k–17.0k lines** | vs 10.5k–16.4k |

Revised **upward** by about 0.9k at the low end, because the shift family came in 58% above the
one-hot measurement and forced a layout change that also touches block C. At ~900 verified lines
per session: **~13–19 more sessions** for Cook–Levin hardness alone. None of this touches
`sat_in_p`; status stays **NOT PROVED**.

## What carries forward vs. what is scratch

**Carry forward:**
* `decS` ([LIB]).
* The **position-function clause machinery**: `clits pos`, `Mono`, `bnd`, `inc_drop`, `bnd_lt`,
  and `lit_run`/`lits_run`/`clause_run` with a per-literal base counter `BS`. It is strictly more
  general than D3OneHot's `CL.off` version and supersedes it: any clause whose literals are
  `counter + constant` fits.
* The **situation-variable design** (C3/C4 change), and the in-range/overflow split by `m = max p c`.
* The block pattern:
  * label chains over the table-indexed dimensions (`i`, `k`);
  * runtime `stLoop`s inside each block;
  * a `Fin (d+1)` decrement chain for `H − m`.
* **Sub-inductive labels** (`ST`, `BD`) under a small top `GL`, needed for `deriving Fintype`.
* **`linarith` (not `nlinarith`) for monomial collapses.** D3OneHot's collapse should be switched
  when that file is next touched (not done this session; it was not in scope).

**Scratch** (to be superseded):
* D3Shift.lean as a file: exploratory, not a root, imports D3OneHot through a scratch `.olean`
  until D3OneHot is a root.
* Its `CK` counter set and labels (the real generator merges all families).
* The draft C3 layout with `sa` inside the `A` block.
* The abstract tables `sa, pl, cn`.
* The bound constants (`litE … shBound`, 591, exponent 7).
* The unary inputs `Tn`/`Hs` and the non-clean halt at `done`.

---

# SITUATION VARIABLES: DESIGN FIXED (session of 2026-09-29) — written BEFORE any code

## Lakefile

* **Applied (approved last session's diff):**
  ```
  -roots = ["Challenge", "Comp", "CookLevin", "SatInP", "Solution", "Prog", "D3Fam"]
  +roots = ["Challenge", "Comp", "CookLevin", "SatInP", "Solution", "Prog", "D3Fam", "D3OneHot"]
  ```
  `lake build` → `✔ [1261/1262] Built D3OneHot (231s)`, `Build completed successfully (1262 jobs).`
  Only warnings: the three known `declaration uses 'sorry'` (Challenge.lean:3, CookLevin.lean:803,
  SatInP.lean:15).
* **Adding `D3Shift`: printed, not applied** (stop-and-wait rule; see the end of this section).

## D1. What `S[t,i]` means

* A **situation** `i < N` is a tuple `(la i, wa i)`:
  * `la i < A₀` is a **combined (label, state) code**;
  * `wa i k j < g` is the symbol code (0 = ⊥) at depth `j < d` of stack `k < KK`.
  * It carries its effect `(na i, pl i k, cn i k, pushed i k)` from B3's `sitStep`:
    * `na i`: the next combined code;
    * `pl i k`: symbols pushed and still on top;
    * `cn i k`: net original symbols consumed;
    * `pushed i k j`: the code of pushed symbol `j < pl i k`.
* **Row `t` is in situation `i`** iff `X[t, la i]` holds and `C[t,k,j,wa i k j]` holds for all
  `k < KK`, `j < d`.
* **`S[t,i]` (for `t < T`, `i < N`) is a Tseitin variable with one-directional meaning: "row `t` in
  situation `i` ⇒ `S[t,i]`".** No clause forces `S[t,i]` false.

## D2. Encoding (draft C3 layout, version 2)

Row width `W = A + KK·H·g` with `A = A₀ + N`, which splits into two blocks:

| offsets in a row | content |
|---|---|
| `[0, A₀)` | combined (label, state) one-hot: `A₀ = (|Λ|+1)·|σ|` (label `none` included) |
| `[A₀, A₀+N)` | situation block |
| `[A, W)` | cells `C[·,k,j,x]` at `A + (k·H + j)·g + x` (unchanged) |

**`S[t,i]` := `xIdx H (t+1) (sa i)` = `(t+1)·W + sa i`, with `sa i = A₀ + i`.** The situation
variable of step `t` therefore lives in the situation block of **row `t+1`**:
* row `0`'s situation block is unused (no clause mentions it);
* rows `1..T` hold `S[0..T−1]`;
* `numVars = (T+1)·W` is unchanged, and no extra row is needed.

In Lean, `sa` stays an abstract table with `sa i < A` (the only property any proof uses).

**Two corrections to P2 that this forces:**
1. P2 counted `A = |Λ|+1+|σ|` (separate label and state one-hots, with `2·T·S₀` update clauses).
   D3Fam was built with **one** `la i` literal per situation, i.e. a combined code. The combined
   code is the design from now on: `A₀ = (|Λ|+1)·|σ|` (still a constant), and there is one update
   family, not two.
2. `A` gains `N` (a constant).

## D3. Defining clauses (the S-definition family)

For `t < T`, `i < N` (time-major, then situation):

`¬X[t, la i] ∨ ⋁_{k<KK, j<d} ¬C[t, k, j, wa i k j] ∨ S[t,i]`

Sorted positions:
* `t·W + la i`
* `<` the cells of row `t`, in `(k, j)` order
* `<` `(t+1)·W + sa i`

**This is exactly `D3Fam.family L la sa wa T H N`**: D3Fam's clause with `na := sa`. Its head
`X[t+1, na i] = (t+1)·W + na i` *is* `S[t,i]` under this layout. D3Fam's `WF` needs `na i < A`,
which becomes `sa i < A`. So the S-definition generator is D3Fam's generator with a different
table. Nothing new is needed; the statement is re-proved as an instance (below).

## D4. Why row `t+1` and not row `t` (the design choice)

Last session's D3Shift put `S[t,i]` at `xIdx H t (sa i)` (row `t`).

| | S in row `t` (last session's draft) | **S in row `t+1` (chosen)** |
|---|---|---|
| S-definition clause | head literal in the *middle*: `X[t,la] < S[t,i] < cells(t)` | head literal *last*: identical to D3Fam |
| S-definition generator | a new, re-targeted D3Fam: `litPos`, polarity, sortedness and machine literal chain all change (est. 300–600 family lines + ≈ 150 bound) | **none**: an instance of D3Fam (≈ 20–40 lines of instantiation) |
| shift clause `¬S ∨ ¬C[t] ∨ C[t+1]` sorted order | `S < C[t] < C[t+1]` (as built) | `C[t] < S < C[t+1]`: D3Shift must be **re-targeted** (new base counter `TW1 = (t+1)·W`, literal order, `Mono` proof) |
| overflow / pushed-fill `¬S ∨ C[t+1]` | `S` first | `S` still first |
| soundness/completeness argument (C5/C6) | identical | identical (it is only a variable numbering) |

The re-target of D3Shift is local: it touches `BS`, `CL.bs`/`CL.cs`, `shPos`/`ovPos`, their `Mono`
proofs, the `Body` invariant, and the time-loop body. Its clause *count* is unchanged. **So row `t+1`
is chosen.** Its cost is measured this session as the D3Shift delta.

## D5. How `S` interacts with each family (replace / alongside / count changes)

| family | status | interaction with `S` |
|---|---|---|
| cell one-hot (D3OneHot) | built | **Unchanged.** Cells only; `A` is a parameter. No line or count change. |
| label/state one-hot | not built | Must range over `[0, A₀)` **only**: the situation block must not get one-hot clauses. It is a constant-size block per row (`1 + A₀(A₀−1)/2` clauses). |
| label/state update (D3Fam, `na`) | built | **Kept alongside, unchanged**: `¬X[t,la i] ∨ ⋁¬C[window] ∨ X[t+1,na i]`, without `S`. The short form `¬S[t,i] ∨ X[t+1, na i]` would also do, but D3Fam is already built and proved. |
| **S-definition** | **this session** | `D3Fam.family` with `na := sa`: one clause per `(t,i)` |
| cell shift + overflow (D3Shift) | built, **re-targeted** this session | `¬S[t,i] ∨ ¬C[t,k,u+c,x] ∨ C[t+1,k,u+p,x]` and `¬S[t,i] ∨ C[t+1,k,H−c+p+r,⊥]`. `S` moves to row `t+1`; the counts are unchanged. |
| pushed fill | not built | `¬S[t,i] ∨ C[t+1,k,j,pushed i k j]` for `j < pl i k`: one clause kind with constant offsets, the same shape as the overflow clause. It fits D3Shift's `CL` as a third kind. |
| halted-idle | not built | **Subsumed.** Halted rows (label `none`) become situations too: `la i = (none, v)`, `na i = la i`, `pl = cn = 0`, all windows. Then the shift family with `p = c = 0` *is* the idle copy, and the update family keeps the code. There is no separate family. `N = (|Λ|+1)·|σ|·g^{KK·d}` (a constant). |
| init, accept | not built | Do not mention `S`. |

Clause-count effect on P2: `+T·N` S-definition clauses. The transition constraint uses `S` instead
of `KK·d`-literal situation prefixes, and idle is subsumed. Each of these is a constant factor, so
P2's degrees (`4E` size, `≤ 6E` generation time) are unchanged.

## D6. Obligations this puts on C5/C6 (to be proved there, not now)

* **C5 (completeness).** Set `S[t,i] :=` "row `t` of the real run is in situation `i`". The
  S-definition clauses then hold: if the situation does not hold, some label/window literal is
  false by one-hot. Every consumer of `S` holds by C2. Set row `0`'s situation block to `false`
  (it is unconstrained).
* **C6 (soundness).** Row `t` decodes (one-hot) to a config that is prefix-form and in range. It is
  in exactly one situation `i`, and the enumeration is complete over `(code, windows)`, so the
  S-definition forces `S[t,i]`. The consumers of `i` then force every cell of row `t+1` and its
  code; one-hot at `t+1` makes that exact. Spurious `S[t,i'] = true` only adds constraints, so it
  cannot help an unsatisfiable instance. The height precondition comes from A5 on the real run,
  by induction on `t`.

## D7. Line-count estimates recorded before this design change: affected?

* **D3OneHot (626 family + 146 bound): not affected.** The situation block only enlarges the
  constant `A`, which the family takes as a parameter. Its clauses and machine do not change.
* **D3Fam (≈ 600 family + 145 bound): the lines are not affected, but what they buy changes.**
  The same file now provides **two** families of Φ: label/state update (`na`) and S-definition
  (`sa`). The P6 row "remaining: situation definition ≈ D3Fam variant, 350–700" is therefore
  **replaced by the instantiation cost (measured below) plus the D3Shift re-target delta**.
* **The P2 correction** (combined code, one update family instead of two) removes nothing that was
  counted separately in P6: P6 already counted one "label/state" update family.
* **The idle family** (counted in P6's "remaining: 5 × 350–700") is subsumed by D5. That removes one
  of the five remaining families.
* **D3Shift (990 + 177):** the re-target delta is measured this session.

## Target for this session (fixed before code)

1. **D3Shift re-targeted**: `S[t,i]` at `xIdx H (t+1) (sa i)` in `shLits`/`ovLits`. `sh_time` must
   still be proved with **the same statement shape**; the constant `shC` may change.
2. **New file `D3SDef.lean`** (exploratory, imports D3Shift), containing:
   * `sdLits`/`sdFamily`: the S-definition family stated **independently**, from `sIdx`
     (= `xIdx H (t+1) (sa i)`), `xIdx`, `cIdx`;
   * `sdFamily_eq : sdFamily L la wa sa T H N = D3Fam.family L la sa wa T H N`;
   * `sd_time`: with `WF` for `(la, sa, wa)`, the finite-labelled generator (`D3Fam.prog L la sa wa N`,
     whose `genTM` is a `FinTM2`) emits `encodeCNF (sdFamily …)` within `genC L N·(T+H+1)^5`
     steps;
   * `sIdx_shLits`/`sIdx_ovLits`: the `S` literal of D3Shift's clauses *is* `sIdx` (so the two
     families share the same variable, stated in Lean, not just in these notes);
   * `sd_sorted`: the S-definition literal list is strictly increasing and in range (inherited).
3. Each new declaration gets `#print axioms`. Banned-token scan on the touched files. `lake build`
   is clean after each step.

## Outcome: target met as stated

**1. D3Shift re-targeted.**
* `S[t,i]` is now at `xIdx H (t+1) (sa i)`, and the in-range literal list is in the sorted order
  `[C[t,k,u+c,x]⁻, S[t,i]⁻, C[t+1,k,u+p,x]⁺]`.
* New counter `TW1 = (t+1)·W`, computed per time step by two `copyS` and drained at `tEnd2`.
* `BS.tw` became `BS.s` (base `TW1`). `Body` gained the field `TW1`.
* `sh_time` is proved with **the same statement**; only `shC` changed, 591 → 616 (`+25` = the extra
  `2·(2V+2) + (V+1)` per time step at `k = y = 1`).
* Correctness proofs went through **on the first compile**. Fix rounds: 1 (the collapse constant)
  plus 1 linter warning (`<;>` → `;`).
* `lake env lean D3Shift.lean`: `exit=0`, no errors, no warnings (1m16s).

**2. `D3SDef.lean` (133 lines, new).**
* `sIdx`, `winLits`, `sdLits`, `sdFamily`: the family, stated independently.
* `flatMap_range_divmod`: the `(k, j)` enumeration equals the `n ↦ (n / d, n % d)` enumeration.
* `sdLits_eq`, **`sdFamily_eq : sdFamily L la sa wa T H N = D3Fam.family L la sa wa T H N`**.
* `sd_sorted`.
* `sdTM : Turing.FinTM2` (finite labels) and **`sd_time`**, the time-bound target as fixed:
  `genC L N · (T+H+1)^5` steps, output `encodeCNF (sdFamily …) ++ o`.
* `shLits_S`, `ovLits_S` (`rfl`): D3Shift's `S` literal **is** `sIdx`.
* `sIdx_block`.
* Checked against a scratch `D3Shift.olean` (`lean -o` into the session scratchpad, with
  `LEAN_PATH` prefixed): `exit=0`, no output. Fix rounds: 1 (two errors: `congr` had already closed
  the head goal, and `FinTM2` needed the `Turing.` prefix).

**Checks (all run this session, output quoted):**
* `#print axioms` on **every** declaration, from scratch copies with generated lines:
  * D3Shift, 98 declarations: 22 × `[propext, Classical.choice, Quot.sound]`, 21 ×
    `[propext, Quot.sound]`, 4 × `[propext]`, 51 × none. This is the same profile as before the
    re-target. E.g. `'PvsNP.D3SH.sh_time' depends on axioms: [propext, Classical.choice,
    Quot.sound]`, and likewise `sh_run`, `tbody_run`, `xs_run`, `obody_run`, `shBound_le`.
  * D3SDef, 13 declarations: `sd_time`, `sdFamily_eq`, `sdLits_eq`, `sd_sorted`, `sdTM` and
    `sIdx_block` → `[propext, Classical.choice, Quot.sound]`; `flatMap_range_divmod` →
    `[propext, Quot.sound]`; `sIdx`, `winLits`, `sdLits`, `sdFamily`, `shLits_S` and `ovLits_S` →
    `does not depend on any axioms`.
  * No `sorryAx` anywhere.
* Banned-token scan (the usual pattern) on D3Shift.lean, D3SDef.lean and lakefile.toml: no
  matches.
* Final `lake build`: `Build completed successfully (1262 jobs).`, only the three known `sorry`
  warnings. D3Shift and D3SDef are not roots, so `lake build` does not check them; the runs above
  do.
* **No `#eval` evidence this session.** The run theorems are the result. The previous sessions'
  `#eval`s were run against the pre-re-target D3Shift and do not cover the new literal order.

## Line counts (the same categories as before)

| | S-definition family (D3SDef) | D3Shift re-target (delta) |
|---|---|---|
| **family-specific correctness** | **≈ 75**: spec 20, equality to D3Fam 25, instance (`sdTM`, `sd_time`) 12, shared-variable lemmas 18 | **+66 / −45**: spec + doc 13, counters/labels 9, positions + `Mono` 8, `Body` 6, per-body position proofs 4, `sh_run` call 1, `tbody_run` rewrite ≈ 25 |
| **time bound** | **0** new lines: `genC·(T+H+1)^5` is inherited; only the ≈ 2-line statement | **+5 / −5** (`tBodyB` gains 3 terms in 2 rewritten lines; constant 591 → 616 in 3 lines) |
| **new reusable library** | ≈ 20 (`flatMap_range_divmod`; C4/C7 will need the same `(k,j) ↔ n` bijection) | 0 |
| header / doc | ≈ 30 | — |

Net: D3SDef.lean is 133 lines; D3Shift.lean goes 1206 → 1227 (+71 / −50).

**Fair comparison.** This family is **not** an independent measurement like the other three
(D3Fam ≈ 600 + 145, one-hot ≈ 626 + 146, shift ≈ 990 + 177). It fills a gap by **reuse**. Under the
chosen layout its clause *is* D3Fam's, so all machine and loop-invariant work was already paid for.
What it measures is:
1. the cost of proving a restated family equal to an existing one (≈ 45 lines, including the div/mod
   bijection);
2. the cost of moving one literal of an existing family (≈ 70 changed lines, first-try correct).

The counterfactual, keeping `S` in row `t` as last session drafted, would have needed a
re-targeted D3Fam with its head literal in the middle: new `litPos`, polarity, sortedness and
literal chain. By the D3Fam per-section costs that is ≈ 300–600 family lines + ≈ 150 bound lines.
**The layout choice saved ≈ 0.4k–0.7k lines**, not the family being cheap.

## Is the transition constraint now complete? (reassessment before C3–C6)

Paper check of C6 (row `t` decodes to the real config `c_t` ⇒ row `t+1` is forced to `step c_t`):

| what row `t+1` needs | forced by | status |
|---|---|---|
| `S[t,i]` for the unique situation `i` of row `t` | S-definition (window ⇒ `S`) | **built** (D3SDef) |
| next combined (label, state) code | update family `D3Fam.family L la na wa` | built (D3Fam) |
| cells at target depths `[0, p)` | pushed fill `¬S ∨ C[t+1,k,j,pushed i k j]` | **not built** (known; the same shape as overflow) |
| cells at `[p, H − c + p)` | in-range shift | built (D3Shift) |
| cells at `[H − c + p, H)` (only `c > p`) | overflow ⊥-fill | built (D3Shift) |
| halted rows (label `none`) | halted situations (`p = c = 0`, `na = la`) | **subsumed**, no family (D5) |
| exactness (one code per cell/row) | one-hot at `t+1` | cells built (D3OneHot); label/state one-hot over `[0, A₀)` not built |

Coverage of target depths: `p + (H − m) + (c − p)⁺ = H` with `m = max p c ≤ d ≤ H`. It is exact
and disjoint (checked by hand in both cases `c ≤ p` and `c > p`; not yet a Lean lemma; C2 needs it).

**Answer: no new design gap in block C's transition constraint.**
* Its complete clause list is: update + S-definition + shift/overflow + pushed fill.
* **Only pushed fill is unbuilt**, and it is a known piece.
* Idle drops out as a separate family.

This session found two smaller issues, both resolved above:
1. **A P2/D3Fam inconsistency.** P2 assumed separate label and state one-hots (`A = |Λ|+1+|σ|`,
   two update families), but D3Fam uses one combined code per situation. Fixed to the combined code
   (`A₀ = (|Λ|+1)·|σ|`, one update family).
2. **The label/state one-hot must skip the situation block.** So the layout needs `A₀` as well as
   `A` (the one-hot family will take `A₀ ≤ A` as a parameter). This is a layout detail, not a family
   change.

Also checked this session: the repo's `pair_encoding` is `w.map inl ++ inr none :: y.map (inr ∘
some)`, and `InNondeterministicPolynomialTime` uses `fin_encoding_string Γ₁` (identity) for the
certificate. So row 0's input stack is exactly P3's `w # y`, and the init family has no encoding
surprise.

**Where a gap could still hide** (not in clause *shapes*; in proofs not yet started):
1. **B1/B3 formalization.** `sitStep` must be defined on `Option Λ` (identity on `none`) for the
   idle subsumption. Situations with codes invalid for a stack need arbitrary but well-typed tables.
2. **C6's decoding.** Invalid codes (`x ≥ |Γfin k| + 1`) must be excluded at row 0 by the init
   family. Later rows inherit validity by induction.
3. **The halting shape.** The verifier's `TM2OutputsInTime` reaches `haltList`: label `none`, state
   `initialState`, **every non-output stack empty**. Accept therefore only needs `none` + output
   `[true]`. A3's idle-extended `run` must match Mathlib's `EvalsTo` step semantics.

None of these changes C3's layout or C4's family list.

## Updated P6 / D-block estimate (supersedes the third 2026-09-28 table)

| Block | Estimate | Basis |
|---|---|---|
| D1 library | ≈ 1.2k (958 + 209 + 10 + 20) | measured |
| D3 families, measured | 600 + 626 + 1011 + 75 ≈ 2.3k | four measurements (the 4th by reuse) |
| D3 families, remaining | pushed fill 100–250 (a 3rd `CL` kind in the shift generator; **unmeasured**); label/state one-hot over `[0,A₀)` 350–600; accept 200–400; init + input decoding (new primitive: an input symbol into the label) 600–1000 → **≈ 1.25k–2.25k** | was 5 × 350–700 = 1.8k–3.5k: S-definition now built, idle subsumed |
| time bounds | measured 145 / 146 / 177 (unchanged size) / 0; remaining ≈ 20 + 3 × 150–200 → **≈ 0.95k–1.1k** | was 1.2k–1.5k |
| finite labels + top-level composition (concatenating the family generators) + clean halt | 300–600 | unchanged |
| D4 glue | 200–400 | unchanged |
| D2 (`unaryBound`), link to verifier tables | 400–600 | unchanged |
| **D total** | **≈ 6.6k–8.5k** | vs 7.3k–10.0k |
| A + B + C | 4.1k–7.0k | unchanged: the `S` design is now fixed; idle subsumption removes a C6 case but B3 gains `none` situations |
| **Total** | **≈ 10.7k–15.5k lines** | vs 11.4k–17.0k |

Revised **down**, by ≈ 0.7k at the low end and ≈ 1.5k at the high end. The reduction is from:
* the layout choice (S-definition by reuse, instead of a new family);
* idle being subsumed;
* pushed fill folding into the shift generator. **This last part is unmeasured, i.e. optimistic
  until built.**

**Session count, corrected method.** The earlier "~13–19 more sessions" divided the *total* by
~900 lines/session. That overcounts, because ≈ 4.0k of the estimated lines already exist (D1 +
library 1.2k, four families 2.3k, bounds ≈ 0.47k). **Remaining ≈ 6.7k–11.5k lines ⇒ ≈ 8–13
sessions** at ~900 verified lines/session. By the old method (total/900) it would be ≈ 12–17.

None of this touches `sat_in_p`; status stays **NOT PROVED**.

## What carries forward vs. what is scratch

**Carry forward:**
* **The fixed design:**
  * `S[t,i] = xIdx H (t+1) (sa i)` (row `t+1`, situation block `[A₀, A₀+N)`);
  * the combined (label, state) code;
  * halted situations in place of an idle family;
  * the transition family list (D5).
* The re-targeted D3Shift's pattern of **one base counter per literal kind** (`TW1` added without
  touching the loop proofs). Adding a literal base costs ≈ 30 lines in the time body.
* `flatMap_range_divmod` ([LIB]).
* **Reuse by restated-spec + equality proof.** State a family in its own terms, then prove it equal
  to an existing generator's family. It cost ≈ 45 lines here; check for it before building any
  "variant" family.

**Scratch** (to be superseded):
* D3SDef.lean as a file;
* the abstract tables `la, sa, wa, pl, cn`;
* the bound constants (`616`, `323`);
* the per-family `CK` counter sets;
* the non-clean halt.

## Lakefile

The `D3Shift` root addition is **printed here and not applied**, per the stop-and-wait rule (each
lakefile change needs its own reply):
```
-roots = ["Challenge", "Comp", "CookLevin", "SatInP", "Solution", "Prog", "D3Fam", "D3OneHot"]
+roots = ["Challenge", "Comp", "CookLevin", "SatInP", "Solution", "Prog", "D3Fam", "D3OneHot", "D3Shift"]
```
`D3SDef` would need the same treatment later. I am not asking for that now.

---

# PUSHED FILL (session of 2026-09-29, second) — spec written BEFORE any code

## Lakefile

* **Applied (approved in the user's message this session):**
  ```
  -roots = ["Challenge", "Comp", "CookLevin", "SatInP", "Solution", "Prog", "D3Fam", "D3OneHot"]
  +roots = ["Challenge", "Comp", "CookLevin", "SatInP", "Solution", "Prog", "D3Fam", "D3OneHot", "D3Shift"]
  ```
  Build result recorded under "Outcome" below.

## The clause family (precise)

New verifier table `pu i k j` = code (in `[1, g)`; `0` is ⊥) of the pushed symbol at target depth
`j` of stack `k` in situation `i` (B3's `pushed i k j`, top-indexed: `j = 0` is the new top).

For `t < T`, `i < N`, `k < KK`, `j < p` (with `p = pl i k`):

`¬S[t,i] ∨ C[t+1, k, j, pu i k j]`, positions `(t+1)·W + sa i  <  (t+1)·W + A + (k·H + j)·g + pu i k j`.

It covers exactly the target depths `[0, p)` of stack `k` in row `t+1`, the one region the shift
family leaves out. Together with in-range `[p, H − c + p)` and overflow `[H − c + p, H)` (only
`c > p`), every depth `j < H` of every stack is covered (to be stated as a Lean lemma this session,
`depth_cover`, since C2/C5 need it).

`WF` gains `pu_lt : ∀ i < N, ∀ k < KK, ∀ j < pl i k, pu i k j < g`. `j < p ≤ d ≤ H` is already in `WF`.

## Is it "the same shape as the overflow clause"? (checked while writing the spec, before code)

| aspect | overflow | pushed fill | same? |
|---|---|---|---|
| literals | `¬S[t,i]`, `C[t+1,k,·,·]⁺` | same | **yes** |
| sorted order / `Mono` proof | `S` block < row `t+1` cell | same argument | **yes** |
| depth index | `H − c + p + r`, `r` a **runtime** loop (depends on `H`) | `j < p ≤ d`, a **constant** | no: simpler |
| symbol code | constant `0` | table `pu i k j` (depends on `j`) | no: needs a new table |
| boundary handling | needs the height precondition (source above the cap) | **none**: target always in range, no source literal | no: simpler |
| machine | `stLoop` over `R` + `(U+r)·g` multiply per iteration | **label chain over `j : Fin d`** (like the `x` chain), one base setup per block | different, but an existing pattern |

So: the clause **shape** claim holds exactly; the **generation** does not reuse the overflow loop.
Because `(j, pu i k j)` are both table constants, the natural fit is a third `CL` kind
`pf (j : Fin d)` whose literal-1 offset is the constant `j·g + pu i k j` off the base `CW := KB + W`,
emitted by a label chain like `xs_run`. No boundary case, no runtime loop. Prediction before code:
this should be **cheaper** than overflow (≈ 100–250 lines as estimated), with the main costs being
(a) threading a new table `pu` through D3Shift's signatures, (b) `CL g → CL g d`, `BD g → BD g d`
(`Fin d` in the clause kind, for `deriving Fintype`), (c) ≈ 8 setup/drain stages.

## Placement

Built **inside D3Shift.lean** as a third clause kind (not a new file): the literal/clause routines
(`lit_run`, `clause_run`) are proved for D3Shift's `prog`, and a separate generator would duplicate
them. Output order per block: in-range ++ overflow ++ pushed fill (machine runs fill first; everything
is prepended). `shFamily`, `sh_time` keep their shape with the extra table `pu`; `shC` may change.

## Outcome: pushed fill built and proved

**Lakefile.** Applied as approved. `lake build` then printed `✔ [1262/1263] Built D3Shift (186s)`
and `Build completed successfully (1263 jobs).`. The only warnings were the three known
`declaration uses 'sorry'` (Challenge.lean:3, CookLevin.lean:803, SatInP.lean:15). From now on
`lake build` checks D3Shift.

**What was built** (all in D3Shift.lean, 1227 → 1375 lines):
* **Spec:**
  * `pfLits`;
  * `shBlk` = in-range ++ overflow ++ **pushed fill** (`(List.range (pl i k)).map … pfLits …`);
  * `WF.pu_lt`.
* **Coverage:**
  * `depth_cover`: every `j < H` is `< p`, or `u + p` with `u < H − m`, or `H − c + p + r` with
    `r < c − p`;
  * `depth_disjoint`: the regions are disjoint and in range.
  * These turn last session's hand-checked coverage into Lean lemmas. C2/C5 will use them.
* **Machine:**
  * clause kind `CL.pf (j : Fin d)` (so `CL g → CL g d` and `BD g → BD g d`), with `nl = 2`,
    base `[s, cw]`, offsets `[sa i, j·g + pu i k j]`;
  * 5 setup stages (`fC1 fC2 fW1 fW2 fD1`: `CW := KB + W`, chain, drain);
  * label chain `GL.pfFrom`;
  * `sbL` now leads into the fill setup, and the fill leads into the overflow setup.
* **Proofs:**
  * `kbw_le`, `pfPos`, `pfPos_mono`, `clits_pf`;
  * `pf_run` (the chain; an induction like `xs_run`);
  * the fill segment inside `ik_run`;
  * `encodeCNF_shBlk` with its third part.
* **Statement:** `sh_time` keeps its shape, with the extra implicit table `pu`. `shC`: 616 → **828**
  (exact: `#eval shBound (Layout.uni 1) 1 1 1` = `828`). The same 30-monomial `linarith` closes the
  collapse; no new monomials were needed.
* **D3SDef:** `pfLits_S` (`rfl`): the fill clause's `S` literal is `sIdx`.

**Fix rounds: 3**, none of them mathematical:
1. Three errors: a `CL L.g L.d` type ascription in `clits_sh`, an unused hypothesis, and one
   `funext` case that needed `omega`.
2. `++` is **left**-associative, so `a ++ b ++ o` needed explicit parentheses to match `stLoop`'s
   output.
3. Two `<;>` linter warnings.

Also, a first-draft setup (copy `KB → CB → CW`, add `W`) was simplified to `KB → CW`, add `W`. `CB`
is not needed because every fill literal is based on `S` (`TW1`) or `CW`.

I first wrote the constant as 843, a hand estimate. `linarith` accepted it because it is a valid
upper bound. The `#eval` showed that the exact coefficient sum is 828, so the constant was tightened
and the file re-checked.

**Checks (all run this session, output quoted):**
* `lake env lean D3Shift.lean`: no output, `exit=0` (1m21s).
* `lake build` (after the final edit): `✔ [1262/1263] Built D3Shift (73s)`,
  `Build completed successfully (1263 jobs).`, with only the three known `sorry` warnings.
* `lake env lean -o <scratch>/D3SDef.olean D3SDef.lean`: `exit=0`.
* `#print axioms` on **every** declaration of D3Shift (108) and D3SDef (14). This was a generated
  scratch file `import D3SDef` + 122 `#print axioms` lines, run with `LEAN_PATH` prefixed by the
  scratch dir. Results:
  * 31 × `[propext, Classical.choice, Quot.sound]`, 26 × `[propext, Quot.sound]`, 4 × `[propext]`,
    61 × none. **No `sorryAx`.**
  * New declarations: `pf_run`, `ik_run`, `sh_run`, `sh_time`, `shBound_uni`, `shBound_le`,
    `depth_disjoint`, `GL.pfFrom_succ` → `[propext, Classical.choice, Quot.sound]`;
  * `depth_cover`, `kbw_le`, `pfPos_mono`, `clits_pf`, `encodeCNF_shBlk`, `prog` →
    `[propext, Quot.sound]`;
  * `pfLits`, `pfPos`, `GL.pfFrom`, `WF`, `CL.cs`, `CL.nl`, `D3SD.pfLits_S` → none.
* Banned-token scan (the usual pattern) on D3Shift.lean, D3SDef.lean and lakefile.toml: no matches.

**Evidence (not proof).** `#eval` of the real machine (`TM2.step` iterated to a stop). In all 8
instances the output equals `encodeCNF (shFamily …)`, the final label is `none`, and the step count
is `≤ shBound`.

| ⟨A,KK,g,d⟩ N T H, tables | steps | `shBound` | clauses (of which fill) |
|---|---|---|---|
| ⟨3,2,3,2⟩ 2 2 3; `p ∈ {1,2}`, `c ∈ {0,1}`, codes 1–2 | 235027 | 1448512 | 52 (10) |
| ⟨2,1,3,2⟩ 2 2 3; `p = c = 2` | 26803 | 226409 | 20 (8) |
| ⟨1,1,2,2⟩ 1 2 3; `p = 0, c = 2` (no fill) | 5519 | 41593 | 8 (0) |
| ⟨1,1,2,2⟩ 1 1 2; `p = d = H = 2` (fill only) | 512 | 5568 | 2 (2) |
| ⟨2,2,1,1⟩ 2 2 2; `g = 1` | 8920 | 54316 | 16 (8) |
| `T = 0` / `N = 0` / `KK = 0` | 76 / 268 / 98 | 76 / 760 / 206 | 0 |

Positions check: `pfLits ⟨3,2,3,2⟩ (i ↦ i) (i k j ↦ i+k+j) 3 1 1 1 1 = [(43, false), (60, true)]`.
By hand: `W = 21`, `S = 2·21 + 1 = 43`, cell `= 42 + 3 + (1·3+1)·3 + 3 = 60`.

## Line counts (the same categories as before)

Diff of D3Shift.lean against the session-start copy: **+313 / −165 lines** (net +148). By
category:

| category | net lines | detail |
|---|---|---|
| **family-specific (pushed fill)** | **≈ 124 new** (+ ≈ 90 lines rewritten in place) | spec `pfLits` + `shBlk` + `WF` ≈ 10; labels (`CL.pf`, `nl/bs/cs` cases, 5 `ST` stages, `pfFrom`, `pfFrom_succ`, `nextC` case) ≈ 22; machine stages 6; positions (`kbw_le`, `pfPos`, `pfPos_mono`, `clits_pf`) ≈ 35; `pf_run` ≈ 35; the fill segment in `ik_run` + `encodeCNF_shBlk` ≈ 16. The **rewritten-in-place** lines are the mechanical threading of the new table `pu` (`prog L sa pl cn pu N`, section variables, `WF`, `blkI/blkT`) and `CL g → CL g d`, `BD g → BD g d`. They are real churn (they cost a compile round), but not new proof. |
| **time bound** | **+1** (plus 3 changed lines) | one `ikB` term, `(2V+2) + (2V+2) + d·clauseB V + (V+1)`; the constant 616 → 828 in 3 lines. No new bound lemma: `ik_run`'s closing `omega` got 3 extra facts. |
| **new reusable library** | **0** | nothing new in `[LIB]`. |
| coverage lemma (a C2 obligation, done early) | 18 | `depth_cover`, `depth_disjoint` |
| header / doc | +2 (+4 changed) | |
| D3SDef | +4 | `pfLits_S` + doc |

## Did "same shape as overflow" hold?

* **The clause shape: yes, exactly.** Two literals, `¬S[t,i]` first, one positive row-`t+1` cell;
  the same sorted order and the same `Mono` argument (`pfPos_mono` is a near-copy of
  `ovPos_mono`).
* **The generation: no, but in the cheap direction.** Overflow needs a runtime `stLoop` over `r`
  with a per-iteration multiply `(U + r)·g`, and it relies on the height precondition. In the pushed
  fill, both the depth `j < p ≤ d` and the code `pu i k j` are table constants. It is therefore a
  **label chain** (the `xs_run` pattern) with one base setup per block and **no boundary case**:
  targets are always in range and there is no source literal.
* The costs that were actually new are the table `pu` and `Fin d` inside the clause kind. Both
  touched many signatures, but only mechanically.

**So the assumption behind the optimistic estimate held.** The 100–250 estimate is met at its low
end: ≈ 125 new lines (family + bound), with no independent machinery.

## Completeness pass: the transition constraint, clause kind by clause kind

What C6 needs for row `t+1`, given that row `t` decodes to the real configuration `c_t`:

| clause kind | forces | Lean artifact | status |
|---|---|---|---|
| S-definition `¬X[t,la i] ∨ ⋁¬C[t,window] ∨ S[t,i]` | `S[t,i]` for the actual situation `i` | `D3SD.sdFamily_eq`, `sd_time` | **proved** |
| update `¬X[t,la i] ∨ ⋁¬C[t,window] ∨ X[t+1,na i]` | next combined (label, state) code | `D3Fam.gen_time` | **proved** |
| pushed fill `¬S ∨ C[t+1,k,j,pu i k j]`, `j < p` | target depths `[0, p)` | `D3SH.sh_time` (`pf_run`) | **proved (this session)** |
| in-range shift `¬C[t,k,u+c,x] ∨ ¬S ∨ C[t+1,k,u+p,x]` | `[p, H − c + p)` | `D3SH.sh_time` (`xs_run`) | **proved** |
| overflow `¬S ∨ C[t+1,k,H−c+p+r,⊥]` | `[H − c + p, H)`, only `c > p` | `D3SH.sh_time` (`obody_run`) | **proved** |
| coverage of all depths `j < H`, disjoint | no depth unforced, none double-forced | `D3SH.depth_cover`, `depth_disjoint` | **proved (this session)** |
| halted rows | via halted situations (`p = c = 0`, `na = la`) | none needed (subsumed) | design; needs B3's `sitStep` on `Option Λ` |
| shared variable `S[t,i]` across all consumers | | `shLits_S`, `ovLits_S`, `pfLits_S` (`rfl`) | **proved** |

**Nothing is missing from the transition constraint's clause list:** every kind is generated by a
proved, finite-labelled, polynomially bounded machine.

What "complete" does **not** cover: these are generator facts (the machine emits exactly the stated
family, fast enough). The *semantic* facts, that the families force `step c_t` (C6) and that the
real run satisfies them (C5), are block C and entirely unproved. The families outside the
transition constraint are also still unbuilt:
* label/state one-hot over `[0, A₀)`, needed by C6 for exactness of the code;
* init;
* accept.

## The three known gaps: did any turn non-trivial while building pushed fill?

1. **Locality lemma and situation table for halted labels** (`sitStep` on `Option Λ`, identity on
   `none`). **Untouched, still open and separate** (block B). Pushed fill for a halted situation is
   empty (`p = 0`), so it adds nothing. One **new, small obligation** surfaced: B3 must define
   `pu i k j` as the code of the real pushed symbol (`1 + index`, valid for stack `k`). `WF.pu_lt`
   only asks `< g`, the maximum over stacks. C6's "later rows inherit valid codes" induction needs
   per-stack validity, which holds by construction but must be stated. It is a one-line table
   property, not a gap in the design.
2. **Invalid symbol codes at row 0.** **Unchanged, open and separate** (the init family / C6). The
   pushed fill neither causes nor fixes it; with (1), pushed codes are valid by construction.
3. **Matching Mathlib's final halted configuration** (`haltList`: `none`, `initialState`, all
   non-output stacks empty). **Untouched, open and separate** (A3 / accept / clean halt).

None of the three turned out non-trivial during this session. All three remain open.

## Updated P6 / D-block estimate (supersedes the 2026-09-29 first-session table)

| Block | Estimate | Basis |
|---|---|---|
| D1 library | ≈ 1.2k | measured, unchanged |
| D3 families, measured | 600 + 626 + 1011 + 75 + **124** ≈ 2.45k | five measurements (pushed fill added) |
| D3 families, remaining | label/state one-hot over `[0,A₀)` 350–600; accept 200–400; init + input decoding 600–1000 → **≈ 1.15k–2.0k** | was 1.25k–2.25k; pushed fill moved to measured |
| time bounds | measured 145 / 146 / 177 / 0 / **1**; remaining 3 × 150–200 → **≈ 0.9k–1.05k** | the pushed-fill bound was ≈ 20 estimated, 1 measured |
| finite labels + top-level composition + clean halt | 300–600 | unchanged |
| D4 glue | 200–400 | unchanged |
| D2 (`unaryBound`), link to verifier tables | 400–600 | unchanged |
| **D total** | **≈ 6.6k–8.3k** | vs 6.6k–8.5k |
| A + B + C | 4.1k–7.0k | unchanged; **no measurement exists for any of it**. The coverage lemma (18 lines) is a small down payment on C2. |
| **Total** | **≈ 10.7k–15.3k lines** | vs 10.7k–15.5k |

The estimate moves **slightly down** at the top end, because pushed fill came in at the low end of
its range. The earlier label "optimistic until pushed fill is measured" is resolved: the D3 part of
the estimate is now backed by five measured families.

The **low end does not move**, and the real uncertainty has shifted. The largest unmeasured block is
**A + B + C** (the semantics: B1/B3 situation tables, C5 completeness, C6 soundness). None of it has
been started, and it carries the widest range (4.1k–7.0k). Existing verified lines ≈ 4.15k, so
**≈ 6.5k–11.2k remain ⇒ ≈ 7–13 sessions** at ~900 lines/session.

None of this touches `sat_in_p`, which is the open problem itself; status stays **NOT PROVED**.

## What carries forward vs. what is scratch

**Carry forward:**
* **The complete transition-constraint clause list** (update, S-definition, pushed fill, in-range,
  overflow), all with proved generators, and the Lean coverage lemma.
* **A table-constant index becomes a label chain** (`Fin d` in the clause kind). Use it for any
  clause family whose indices are all table constants.
* `++` is left-associative: build `stLoop`/chain outputs as `a ++ (b ++ o)`.
* **Compute the collapse constant by `#eval shBound (uni 1) 1 1 1`** rather than by hand.

**Scratch:**
* The abstract tables `sa, pl, cn, pu`.
* The constant 828.
* D3Shift's `CK`/label sets. The real generator merges all families.

---

# B3: SITUATION TABLES FROM A REAL `FinTM2` (session of 2026-09-29, third) — spec written BEFORE any code

## Lakefile

No change this session. The new file `Sit.lean` (imports `D3Shift`, a root) is checked with
`lake env lean Sit.lean`; adding it to the roots is printed at the end, not applied.

## S1. Input: an arbitrary `M : FinTM2`

Nothing is assumed beyond the structure: `K` finite with `DecidableEq`, `Λ` and `σ` finite,
`Γ k₀` finite, **`Γ k` for `k ≠ k₀` an arbitrary `Type`** (possibly infinite, no `DecidableEq`),
program `M.m : Λ → TM2.Stmt Γ Λ σ`. `σ` is inhabited (`initialState`).

## S2. Encoding data `Enc M` (a structure; the tables are defined from it)

The tables are functions of an `Enc M`, so that the generic construction is classical but a concrete
machine can supply a computable `Enc` and be checked by `decide`.

| field | meaning |
|---|---|
| `KK`, `kc : K → ℕ`, `kd : ℕ → K` | stack numbering; `kc k < KK`, `kd (kc k) = k`, `kc (kd n) = n` for `n < KK` |
| `A0`, `lc : Option Λ × σ → ℕ`, `ld : ℕ → Option Λ × σ` | combined (label, state) code; `lc x < A0`, `ld (lc x) = x`, `lc (ld c) = c` for `c < A0` |
| `sz k`, `dec k : Fin (sz k) → Γ k`, `enc k : Γ k → ℕ` | finite effective alphabet of stack `k` (B2's `Γfin`); `enc k (dec k i) = i + 1` (code 0 is ⊥) |
| `push_mem` | every symbol that any `push k f` node of any `M.m l` can push (`f v`, any `v`) is some `dec k i` |
| `input_mem` | every `x : Γ k₀` is some `dec k₀ i` (the init family / C6 will need it; not used here) |

`Enc.ofFinTM2 M` (classical, `noncomputable`): `Γfin k` = the finset of pushable symbols of stack `k`
(collected recursively over every statement tree, over all `v : σ`), plus all of `Γ k₀` when
`k = k₀`; codes via `Finset.equivFin`; stacks and labels via `Fintype.equivFin`.

Derived code decoding: `decO k c := some (dec k (c−1))` if `1 ≤ c ≤ sz k`, else `none` (⊥). Codes
`> sz k` (invalid for stack `k` but `< g`) decode to `⊥`: arbitrary but well-typed, as required.

## S3. Constants (all functions of `M` and `Enc M`, no input dependence)

* `d := max_l ops (M.m l)`, where `ops` = the maximum number of `push`/`peek`/`pop` nodes on a
  root-to-leaf path (`branch` takes the max). This bounds net consumption, pushes still on top, and
  read depth (sharpened B1).
* `g := 1 + max_k sz k` (so `0 < g`).
* `G := g^(KK·d)` (number of window combinations), **`N := A0 · G`**.
* `Layout := ⟨A0 + N, KK, g, d⟩`, `sa i := A0 + i` (situation block `[A0, A0+N)`).

## S4. Situation enumeration (explicit mixed radix, computable)

For `i : ℕ`:
* `la i := i / G % A0` (= `i / G` for `i < N`);
* `wa i k j := i / g^(k·d + j) % g` (digit `k·d+j`; used for `k < KK`, `j < d`).

Every `(c < A0, w k j < g)` is hit by exactly one `i < N` (mixed radix). **Surjectivity is what C6
needs ("row `t` is in some situation"); stated as a lemma this session if cheap, otherwise it is an
explicit C6 obligation.**

## S5. The step on `Option Λ` (halted labels without a separate family)

`win i k : List (Option (Γ k)) := [decO k (wa i (kc k) j) | j < d]`.

`sitStep : Option Λ → σ → windows → Option Λ × σ × (∀ k, List (Γ k)) × (K → ℕ)`:
* `sitStep none v W := (none, v, fun _ => [], fun _ => 0)`: **identity on the halted label**, no
  pushes, no consumption. This mirrors the idle-extended run (A3): `TM2.step ⟨none,…⟩ = none` and
  the extended run keeps the config.
* `sitStep (some l) v W := eff W (M.m l) v [] 0`, with `eff` as in the P7 spike (reads come from
  pushed-this-step symbols first, then window entry `j k`; pops of pushed symbols cancel).

With `(l, v) := ld (la i)` and `(l', v', P, c) := sitStep l v (win i)`:
* `na i := lc (l', v')`
* `pl i k := |P (kd k)|`, `cn i k := c (kd k)` (for `k < KK`; `0` otherwise)
* `pu i k j := enc (kd k) (P (kd k))[j]` for `j < pl i k` (`0` otherwise)

## S6. Obligations to prove this session

1. `D3Fam.WF L la na wa H i` for all `i < N` and `D3Shift.WF L sa pl cn pu N H`, given `d ≤ H`.
   Hence `gen_time` (update + S-definition) and `sh_time` apply to the real tables (stated as
   corollaries).
2. `pl, cn ≤ d`: from an `eff` bound, `|P'| ≤ |P| + ops q`, `c' ≤ c + ops q`.
3. **`pu` validity** (stronger than `pu < g`): for `j < pl i k`,
   `1 ≤ pu i k j ≤ sz (kd k)` **and** `decO (kd k) (pu i k j) = some (P (kd k))[j]`, i.e. the code
   decodes, on stack `k`'s own alphabet, to the real pushed symbol. Needs: every symbol in `P` is
   pushable (`eff` preserves "all of `P` is pushable"), then `push_mem` and `enc_dec`.
4. **Halted situations:** if `(ld (la i)).1 = none` then `na i = la i`, `pl i k = 0`, `cn i k = 0`
   (for `i < N`).
5. Concrete check: a small machine (2 stacks, pushes/pops across stacks, halts after a few steps)
   with a computable `Enc`. For every row `t ≤ T` (with `T` past the halting time) of the real
   idle-extended run, the **table-driven row update** (find `i` from the row's code and windows;
   new code `na i`; depth `j < pl` ↦ `pu`, `j < H − cn + pl` ↦ old cell `j − pl + cn`, else ⊥)
   reproduces the next row's codes exactly, checked by `decide` (kernel), with the run including
   rows after halting.

Not this session: B1's proof (`eff` agrees with `stepAux` on real stacks), C2, C5, C6.

## Outcome: tables built for an arbitrary `FinTM2`; all S6 obligations proved

`Sit.lean` (661 lines, **not a root**, imports `D3Shift`). Every S6 item was proved as specified.
Surjectivity (S4) turned out cheap and was proved too.

| S6 item | Lean | status |
|---|---|---|
| encoding record, tables `la wa sa na pl cn pu`, `N`, `layout`, `sitStep` on `Option Λ` | `Enc`, `Enc.{la,wa,sa,na,pl,cn,pu,N,layout}`, `sitStep`, `eff`, `ops`, `depth` | defined |
| real `Enc` for **every** `M : FinTM2` | `Enc.ofFinTM2` (classical: `symSet` = B2's `Γfin`, `Finset.equivFin`, `Fintype.equivFin`) | **defined, no hypotheses** |
| 1. WF for all three generators | `wf_upd`, `wf_sdef`, `wf_sh`; corollaries `upd_time`, `sdef_time`, `shift_time` (the proved `gen_time`/`sh_time` applied to the real tables; hypothesis `depth M ≤ H` only) | **proved** |
| 2. `pl, cn ≤ d` | `eff_bound` (`|P'| ≤ |P| + ops q`, `c' ≤ c + ops q`), `pl_le`, `cn_le` | **proved** |
| 3. `pu` validity | `pu_valid`: for `j < pl i k`, `1 ≤ pu ≤ sz (kd k)` **and** `decO (kd k) (pu i k j) = some x` with `x` the real pushed symbol (`P[j]? = some x`) | **proved** |
| 4. halted situations | `Enc.halted`: `(ld (la i)).1 = none → na i = la i ∧ pl i k = 0 ∧ cn i k = 0` (no `i < N` needed) | **proved** |
| S4 surjectivity | `sit_surj`: every `c < A0` and window codes `w k j < g` give an `i < N` with `la i = c`, `wa i k j = w k j` (via `mix`/`mix_spec`) | **proved** |
| 5. concrete halting example | `ex_halts`, `ex_rows`, `ex_halted_rows`, `ex_neg` (kernel `decide`) | **checked** (evidence) |

**Fix rounds: 4**, none mathematical:
1. `pop` case of `eff_bound`: `simp` left `length ≤ length + 1 + 1` (needed `omega`). Also, `sitStep`
   does not use `E`, so dot notation `E.sitStep` failed; it moved out of the `Enc` namespace and
   takes `M`.
2. `set d := depth M` in `sit_surj` left `depth M` inside the unfolded `G`, and `omega` saw two
   atoms. Also, `simp` rewrote `Fintype.card (Option Λ × σ)` into `(card Λ + 1)·card σ`, which
   broke the `dif`. Fixed with an explicit `rw [dif_pos …]`.
3. The leftover `dsimp only` made no progress (removed).
4. The example's negative-control `#eval` could not synthesize `Decidable` through `let`, so it
   became the theorem `ex_neg`.

`lake env lean Sit.lean`: no output (≈ 55 s).

### Halted labels: covered, not just accounted for (item 4 of the request)

* **General:** `Enc.halted` holds for every `i`. A `none`-labelled situation keeps its code, and
  pushes/consumes nothing on every stack. So the update family copies the code, and the shift
  family with `p = c = 0` copies every cell (in-range `u < H`, no overflow, no fill). No separate
  family is needed.
* **Concrete** (`exM`: 2 stacks, `Bool` alphabet, labels `Fin 2`, state `Option Bool`, `d = 6`,
  `g = 3`, `A0 = 9`, `N = 4 782 969`; input `[true,false,true]`; `H = 16`, `T = 10`):
  * `ex_halts`: label `some 0` at row 6, `none` at rows 7 and 10.
  * `ex_rows`: for **every** `t < 10`, with `i := sitIdx (row t)` (the mixed-radix index of the
    real row's code and windows), all of the following hold:
    * `i < N`;
    * `la i` = the row's code, and `wa i k j` = its window cells;
    * the next real row's code = `na i`;
    * every cell (`k < 2`, `j < 16`) of the next real row equals the table-driven update
      (fill `pu` / shift by `cn − pl` / ⊥).
    Covered: running → running (t = 0..5), **running → halted** (t = 6: `pop` on an empty stack,
    `cn = 1` on `a`, `na = 0` = code of `(none, none)`), and **halted → halted** (t = 7, 8, 9).
    Also covered: push-then-pop cancel on `b`, consumption of an original symbol (`cn = 1` on `b`)
    together with `pl = 2`, and overflow (`c > p` on `a`).
  * `ex_halted_rows`: for `t = 7..9`, `na = la`, `pl = cn = 0` on both stacks (by evaluation).
  * `ex_neg` (**negative control**): a row update that ignores consumption does **not** match the
    run. A second control (`#eval` only) used the wrong situation index `i + 1` for the next code.
    It gave `[false, true, false, true, false, true, false, true, true, true]`, so it fails at
    t = 0, 2, 4, 6. **Correction to a first draft of this note:** it does *not* fail only off the
    halted rows. At t = 1, 3, 5 (label 1, whose `peek` ignores the value read) the `+1` changes only
    window digit `(a, 0)`, and `na` does not depend on it. At t = 7–9 the halted `na` ignores the
    windows. So this control is weak by design; `ex_neg` is the real one.
* `#eval` trace (table values per row, `(la, na, pl a, cn a, pl b, cn b, pu b)`):
  `(3,8,0,1,1,0,[2]) (8,5,0,0,2,1,[1,2]) (5,7,0,1,1,0,[1]) (7,4,0,0,2,1,[1,1]) (4,8,0,1,1,0,[2])
  (8,5,0,0,2,1,[1,2]) (5,0,0,1,0,0,[]) (0,0,0,0,0,0,[]) ×3`.
* `decide` cost: ≈ 1.3 s for `ex_rows` (kernel). All four are `decide`, not `native_decide`.

This is **evidence for one machine**, not B1/C2. The general statement is still owed: `eff` on
the windows agrees with `stepAux` on the real stacks when every height is `≤ H − d`.

### `pu` validity (item 3): needed new work, but little

It did **not** fall out of `WF`. It needed three things:
1. `PushSym` (which symbols a statement tree can push, for **dependent** alphabets:
   `∃ h : k' = k, ∃ v, x = cast (congrArg Γ h) (f v)`) and the `Enc.push_mem` field;
2. `eff_pushed` (an induction on the statement tree: every symbol left in `P` was there before or
   is pushable by `q`);
3. `enc_dec` plus `decO_succ`.

Cost: ≈ 45 lines (`PushSym` 9, `eff_pushed` 33, `res_pushed` 9, `pu_valid` + `decO_succ` 20,
minus overlap). The only real prerequisite was B2's `Γfin` (`symSet`) **containing every pushable
symbol**. It does so by construction, proved in `push_mem_symSet` (≈ 30 lines with `mem_pushFS`).

## Did the real parametric machine need different techniques from D1/D3Fam/D3OneHot/D3Shift?

**Yes, entirely different, and cheaper.** Nothing from the D-block carried over. There is no
machine to program, no loop invariant, no step count, no `Bud` chain, and no collapse arithmetic.
The techniques used were:

| technique | where | friction |
|---|---|---|
| structural induction on `TM2.Stmt` (the Comp.lean `stepAux_lift` pattern) | `eff_bound`, `eff_pushed`, `mem_pushFS` | none; first try except one `omega` |
| dependent alphabets `Γ : K → Type` (casts, dependent `Function.update`) | `PushSym`, `pushFS`, `symSet`, `length_update_le` | **the feared part, but none**: `∃ h : k' = k` + `cast`, then `rcases … rfl` |
| classical finiteness (`open Classical`, `Finset.biUnion`, `Finset.equivFin`, `Fintype.equivFin`) for arbitrary, possibly infinite, non-`DecidableEq` `Γ k` | `symSet`, `Enc.ofFinTM2` | one `simp` normal-form trap (`Fintype.card_prod`/`card_option`) |
| parametrizing by an encoding record (`Enc`) so the same definitions are classical in general and computable on an example | `Enc`, `exE` | none; this is what made the kernel check possible |
| mixed-radix arithmetic | `mix_spec`, `sit_surj` | one `set`/`omega` atom mismatch |

The **parametric-machine unknown** was whether an arbitrary `FinTM2`'s structure could be turned
into finite `ℕ`-tables. The worries were infinite work alphabets, no `DecidableEq`, dependent
stack types, and `none` labels. It **did not bite**. The one design decision that mattered was
separating *what the tables need* (`Enc`: 17 fields) from *how to get it* (`ofFinTM2`).

## Line counts (the same categories as before, where they apply)

| category | lines (total / non-blank non-doc) | content |
|---|---|---|
| **B3 tables, family-specific** | **≈ 370** (all lines incl. doc/blank) | symbolic step `eff`/`ops`/`PushSym` + `eff_bound`/`eff_pushed` (≈ 119), `Enc` + `depth` (58), tables + `sitStep` (28), WF + bounds + validity (83), halted (14), `sit_surj` (30), generator corollaries (36) |
| **B2 (`Γfin`, classical `Enc`)** | **84** (68 non-blank non-doc) | `pushFS`, `mem_pushFS`, `symSet`, membership lemmas, `Enc.ofFinTM2` |
| **reusable library** | ≈ 50 | `mix`/`mix_spec` (mixed radix, 34; C6 and the init family will reuse it); `readTop`, `length_update_le` (16) |
| **time bound** | **0** | not applicable (no machine is built; the corollaries inherit `genC`/`shC`) |
| **evidence [EX]** | 135 (84 non-blank non-doc) | example machine, computable `Enc`, run, row check, negative control |
| header / doc | 25 | |

Total 661 = 370 + 84 + 50 + 135 + 25 (± a few lines of section markers).

**Comparison with the D-block.** The D families cost 600–1000 family lines + 145–177 bound lines
**each**, because each is a hand-built `FinTM2` with step-exact proofs. B2+B3 for a fully
parametric real machine cost **≈ 455 lines in total** (≈ 505 with the reusable library) and took 4
small fix rounds. That is less than one D family's correctness part alone. It is cheaper because it
is ordinary functional Lean about `M`, not a machine that has to be run step by step. **The
parametric machine was not harder than the fixed representative families; it was cheaper.** The real cost of "parametric" shows up elsewhere: in B1/C2
(relating `eff` to `stepAux`) and in C5/C6, which must reason about the whole run.

## Does this change the A+B+C estimate (4.1k–7.0k)?

Only B moves. P6's B row was 600–1000 for B1+B2+B3. Measured: B2 + B3 ≈ 455 lines (plus the
reusable `mix`). This session also built the **symbolic half of B1**: `eff`, `readTop`, `ops` and
the bounds. What remains of B1 is the agreement theorem (`stepAux q v S = ⟨l', v', P ++ drop c⟩`
given windows `take d`), plus B2's `run_mem_Γfin` (every symbol on stack `k` along the run lies in
`symSet M k`, which C5 needs so that `enc` codes are valid). Estimate: B1 agreement 150–300,
`run_mem_Γfin` 60–120. **B total ≈ 0.65k–0.9k** (was 0.6k–1.0k).

**Confidence in the whole 4.1k–7.0k block: essentially unchanged; slightly narrower at the top.**
Reasons:
* B was ≈ 15% of the block and is now largely measured, at its low-middle.
* **C (3.0k–5.0k) dominates and is still completely unmeasured.** C1 cells/decoding, C2
  `cells_step`, C5 and C6 are where the "real run" reasoning lives. Nothing this session measures
  their difficulty. B3 was rated **M** in P4 and came in as mechanical, which says nothing about
  the **H**-rated C6.
* One small positive signal for C: C5/C6 will quantify over `Enc`'s abstract fields (`lc`, `ld`,
  `enc`, `dec`, `kc`, `kd`) and over `sit_surj`. Those interfaces are now fixed and proved to be
  instantiable, so C does not have to reopen B.

**New A+B+C: ≈ 4.15k–6.9k** (B 0.65k–0.9k in place of 0.6k–1.0k). This is within noise of 4.1k–7.0k.

## Updated P6 estimate (supersedes the 2026-09-29 second-session table)

| Block | Estimate | Basis |
|---|---|---|
| D1 library | ≈ 1.2k | measured |
| D3 families, measured | ≈ 2.45k | five measurements |
| D3 families, remaining | ≈ 1.15k–2.0k | unchanged |
| time bounds | ≈ 0.9k–1.05k | unchanged |
| finite labels + top-level composition + clean halt | 300–600 | unchanged |
| D4 glue | 200–400 | unchanged |
| D2 (`unaryBound`), link to verifier tables | **350–550** | was 400–600: the "link to verifier tables" part is now `upd_time`/`sdef_time`/`shift_time` (36 lines, measured) |
| **D total** | **≈ 6.55k–8.25k** | vs 6.6k–8.3k |
| A (plumbing) | 300–500 | unmeasured |
| **B (locality)** | **≈ 0.65k–0.9k**, of which **≈ 0.46k measured** (this session) | was 0.6k–1.0k |
| C (tableau semantics) | 3.0k–5.0k (+ ≈ 0.2k reserve from the old A+B+C range) | **unmeasured** |
| **A + B + C** | **≈ 4.15k–6.9k** | vs 4.1k–7.0k |
| **Total** | **≈ 10.7k–15.15k lines** | vs 10.7k–15.3k |

Verified lines now ≈ 4.15k + 0.53k (Sit.lean without the example) ≈ 4.7k. **Remaining ≈ 6.0k–10.5k ⇒
≈ 7–12 sessions** at ~900 lines/session.

None of this touches `sat_in_p`; status stays **NOT PROVED**.

## Checks (all run this session, output quoted)

* `lake env lean Sit.lean` (final): no output, ≈ 55 s.
* `#print axioms` on **all 75** declarations of Sit.lean (generated scratch file `import Sit`,
  `LEAN_PATH` prefixed with a scratch `Sit.olean`): 34 × `[propext, Classical.choice, Quot.sound]`,
  30 × `[propext, Quot.sound]`, 5 × `[propext]`, 6 × none. **No `sorryAx`.** Examples:
  `'PvsNP.Sit.Enc.pu_valid' depends on axioms: [propext, Classical.choice, Quot.sound]`,
  `'PvsNP.Sit.Enc.halted' depends on axioms: [propext, Quot.sound]`,
  `'PvsNP.Sit.Enc.ofFinTM2' …: [propext, Classical.choice, Quot.sound]`, and the same for
  `shift_time`, `upd_time`, `sdef_time`, `sit_surj`, `ex_rows`, `ex_neg`.
* Banned-token scan (the usual pattern) on Sit.lean and lakefile.toml: no matches (`grep` exit 1).
* `lake build`: `Build completed successfully (1263 jobs).`, with only the three known `sorry`
  warnings (Challenge.lean:3, CookLevin.lean:803, SatInP.lean:15). Sit.lean is not a root, so
  `lake build` does not check it; the `lake env lean` run above does.

## Open items this session surfaced (none blocking)

1. **B1 agreement theorem** (`eff` vs `stepAux`, heights `≤ H − d`) is not proved. It is the
   general form of what `ex_rows` checks on one machine.
2. **B2 `run_mem_Γfin`**: every symbol on stack `k` of the real run lies in `symSet M k`. Without
   it, `cell`'s code of a real symbol is not known to be valid. It follows the same shape as
   `eff_pushed`, but for `stepAux`.
3. **The window read depth.** `readTop` reads window entry `c k`. B1 must show `c k < d` at every
   read. `ops` counts the read node itself, so this holds, but it is part of the agreement proof,
   not yet stated.
4. **`N` is astronomically large for a real verifier** (`A0 · g^(KK·d)`; here 4.8M for a toy). It
   is still a constant, so the polynomial bounds are unaffected. But any end-to-end `#eval` of a
   generator on a real verifier's tables is infeasible. Evidence for C must use toy machines, as
   here.

## Lakefile (printed, NOT applied)

```
-roots = ["Challenge", "Comp", "CookLevin", "SatInP", "Solution", "Prog", "D3Fam", "D3OneHot", "D3Shift"]
+roots = ["Challenge", "Comp", "CookLevin", "SatInP", "Solution", "Prog", "D3Fam", "D3OneHot", "D3Shift", "Sit"]
```

**Applied 2026-09-30** (user approved in the session prompt): `"Sit"` added to roots.

---

# B1: AGREEMENT THEOREM (session of 2026-09-30) — statement written BEFORE any proof

## Lakefile

The diff above was applied at the start of this session (the user approved it in the session
prompt). New B1 code goes **into Sit.lean** (now a root), so this session needs no further lakefile change.

## Re-check of the P3 spike corrections against Sit.lean (before proof)

| Spike / P7 / D3Shift finding | Where it lives in Sit.lean | Status |
|---|---|---|
| shift uses **net** original symbols consumed (push-then-pop cancels) | `eff`, `pop` case: `c` is bumped only when `(P k).isEmpty` | already correct |
| `d` must bound the read depth **and** the pushes still on top | `ops` counts `push`, `peek` and `pop` nodes; `eff_bound` gives `|P k| ≤ ops`, `c k ≤ ops` | already correct (the spike's `d` = pop/peek nodes only was the insufficient version) |
| height 0 (pop/peek on an empty stack) | `readTop` returns window entry `c k`, which is ⊥ past the stack; a pop still bumps `c`, and `drop` past the end is `[]` | handled, and the proof covers it (no case split on height) |
| attention switching between stacks | per-stack `update P k`, per-stack `c k` | handled |
| spike's `pop`: `if isEmpty then P else update P k tail` | Sit: `update P k (P k).tail` | equivalent (`[].tail = []`) |
| halted rows | `sitStep none = (none, v, [], 0)` | new since the spike; matches the idle-extended run |

No fixes needed.

## Statement (two layers; "matches" is made explicit for each)

Notation: `M : FinTM2`, `d := depth M`, `stepI c := (TM2.step M.m c).getD c` (the idle-extended
step: halted configurations stay put, as in A3), and `window c k := (List.range d).map fun j => (c.stk k)[j]?`.

**B1-core (`eff_agree`, symbolic, no hypotheses on the stacks).** For every statement tree `q`,
state `v`, stacks `S0`, windows `W k = window of S0 k`, pushed prefix `P` and consumption `c` with
`c k + ops q ≤ d` for all `k`:
`TM2.stepAux q v (fun k => P k ++ (S0 k).drop (c k))`
`= ⟨r.1, r.2.1, fun k => r.2.2.1 k ++ (S0 k).drop (r.2.2.2 k)⟩` where `r = eff W q v P c`.

**B1 (`step_agree`, FULL configuration equality, no height hypothesis).** For every `c : M.Cfg`,
with `r = sitStep M c.l c.var (window c)`:
`stepI c = ⟨r.1, r.2.1, fun k => r.2.2.1 k ++ (c.stk k).drop (r.2.2.2 k)⟩`.
This is equality of Mathlib `TM2.Cfg` values: label, state, and every stack in full (not just `H`
cells). It needs no height precondition: for short stacks the window is simply ⊥-padded.

**B1-T (`table_agree`, the table-driven step, on the cells the tables track).** For every
`E : Enc M`, `H`, and `c : M.Cfg` with
* (h1) `d ≤ H`,
* (h2) every stack height `≤ H − d`,
* (h3) every symbol on every stack is *encodable*: `∃ n, E.dec k n = x`,

and `i := E.sitIdx c` (mixed radix of `c`'s combined code and its window cell codes):
1. `i < E.N`, `E.la i = E.code c`, and `E.wa i k j = E.cell c k j` for `k < KK`, `j < d` (the
   situation is found);
2. `E.code (stepI c) = E.na i`;
3. for all `k < KK`, `j < H`: `E.cell (stepI c) k j = E.tabRow H i (E.cell c) k j`, where
   `tabRow` is pushed fill (`j < pl`: `pu`), in-range shift (`j < H − max(pl,cn) + pl`:
   `old k (j − pl + cn)`), and overflow ⊥ (`0`), i.e. exactly what the D3Shift clauses force (the same
   `tabRow` the B3 example checked on one machine), and every old cell it reads has index `< H`.

Here "matches" = equality of the combined (label, state) code plus every one of the `KK·H` cell codes of the next row.
Cells are codes (`0` = ⊥, `enc` otherwise), so B1-T is equality **on the cells the tables track**;
B1 above supplies full `Cfg` equality.

**Hypothesis (h3) is stated up front, not added silently.** It is not a hypothesis about the shift
model; it concerns the encoding. A symbol outside `Enc`'s finite effective alphabet has no valid
code (in `ofFinTM2` it gets code `0` = ⊥), so the tables would read the wrong window and B1-T is
false for such configurations. It is exactly B2's `run_mem_Γfin` obligation (open item 2 of the B3 session).
It will be **discharged in this session** for every configuration of the idle-extended run from
`initList M x` (`run_good`, a corollary of B1 + `eff_pushed` + `input_mem`), so the end-to-end
statement for real runs needs only the height hypothesis (h1, h2), which P2's
`H = m + c·T + d + 1` supplies via A5. No family built on the shift model is affected. [**2026-09-30 correction:** the old formula did not provide this when `depth M > pushBound M`; P2 now uses `H = m + (T+1)·d + 1`, and `Sit.capH_height` proves the height precondition for it. See "H CORRECTION + DEPTH_COVER ASSEMBLY".]

**Planned proof shape.** B1-core by induction on `q` (the `eff_bound` pattern), invariant
`c k + ops q ≤ d`, which guarantees every window read `readTop` makes is at index `c k < d` (open item 3 of B3).
B1 = B1-core at `q = M.m l`, `P = []`, `c = 0`, plus the `none` case. B1-T: decode the situation
(`mix_spec`), show `win i = window c` via (h3), then compare cells by cases on `j` (omega on `max`).

## Outcome: B1 proved as stated, with one hypothesis dropped and one discharged

All three layers are proved in Sit.lean (lakefile root). There is no `sorry` and nothing was weakened:

| Layer | Lean | Hypotheses actually used |
|---|---|---|
| B1-core | `eff_agree` | `∀ k, c k + ops q ≤ d` (the in-window invariant). That is all. |
| B1, full `Cfg` equality | `step_agree : stepI M c = applyEff c.stk (sitStep M c.l c.var (winC M c))` | **none**: no height hypothesis, no encodability, any `c : M.Cfg`, running or halted |
| B1-T, table-driven step | `Enc.table_agree` (+ `Enc.sitIdx_spec`, `Enc.tabRow_reads_lt`) | (h2) heights `≤ H − d` and (h3) `Good c` (encodable symbols). **(h1) `d ≤ H` turned out unnecessary** and was dropped: if `H < d` the height hypothesis forces empty stacks |
| B1-T on real runs | `Enc.table_agree_run` | (h2) only; (h3) discharged by `Enc.run_good` |
| B2 `run_mem_Γfin` | `Enc.good_step`, `Enc.good_init`, `Enc.run_good` | none: every configuration of the idle-extended run from `initList M s` is `Good` |

So the **height precondition alone suffices for real runs**. The encodability hypothesis (h3) was
declared in the spec before the proof. It is the B2 obligation, not a property of the shift model,
and it is now discharged. **No stronger hypothesis was needed. Nothing ripples into the D3 families.**

One correction, to an auxiliary lemma only: my first draft of `tabRow_reads_lt` ("every old cell
`tabRow` reads has index `< H`") omitted the branch condition `pl ≤ j` and was **false** (`j < pl`,
`H = 0`: `omega` produced the counterexample). The reads only happen in the `¬ j < pl` branch, so the
lemma now takes `pl ≤ j`. `tabRow` and B1-T are unaffected.

### Did it need new techniques? (the "block B was surprisingly cheap" test)

**No. The cheapness held.** B1-core is one structural induction over `TM2.Stmt` (the `eff_bound`
pattern) with a single arithmetic invariant. Each case is a `funext` + `by_cases k = k₀` + `subst`
stack-update identity. The pop case splits once more on `P k₀` (`List.tail_drop`). It compiled on the
first attempt. `step_agree` needed one fix (eta / `winC` unfolding). B1-T needed no classical finsets
and no new mixed-radix work: `sit_surj`'s proof was refactored into `mix_sit`, which states the
properties of the explicit index, and `sit_surj` is now a one-line corollary. The per-cell comparison is a
generic list lemma `row_cell` (three cases, `omega` with an explicit `max ≤ d` fact). Fix rounds:
3 small ones (the `step_agree` unification, a `congr 3` that went too deep in `row_cell`, and the false auxiliary lemma above).

Where the difficulty went: the invariant `c k + ops q ≤ d` is exactly why `ops` counts every
push/peek/pop node. It guarantees every `readTop` window read is at index `< d` (open item 3 of the B3
session, now proved inside `eff_agree`). Height 0 needed no case split: `drop` past the end is `[]`,
and window entries past the stack are ⊥.

### What "matches" means (restated with the proved forms)

* `step_agree`: **equality of `TM2.Cfg`**: label, state and every stack in full, with
  `stepI c = (TM2.step M.m c).getD c`.
* `table_agree`: equality of the next row's combined code with `na i`, and of **each of the
  `KK·H` cell codes** with `tabRow`. That is equality on the cells the tables track. Cells are `Enc.cell` (`0` = ⊥,
  `enc` otherwise). With `Good` configurations the cell codes are injective on symbols (`decO_cell`), so no
  information is lost inside the tracked window.

### Second machine (evidence, not part of the proof)

`ex2M`: 3 stacks, alphabet `Fin 3`, labels `Fin 3`, state `Fin 4`, `d = 6`, `g = 4`, `A0 = 16`,
`N = 16·4^18`; input `[2,0,1,1]`. The run (`#eval` trace) halts at row 10. It exercises a peek of a symbol
pushed in the same step (label 0), a pop at **height 0** (row 1→2, stack 2), a read at depth 2 below consumed
originals (label 2, stack 1), a push-then-pop cancel on an empty stack 0 (label 2), and `load`. It uses the
**generic** `Enc.sitIdx`/`cell`/`code`/`tabRow`/`stepI`/`runI` from the theorem, not example-local copies.

| check | method | result |
|---|---|---|
| `ex2_rows : ∀ t < 14, row2OK 16 t = true` (height hyp., situation found, `code = na`, all `3·16` cells `= tabRow`) | `decide` (kernel) | proved |
| `ex2_halts` (running at row 9, halted at 10 and 14) | `decide` | proved |
| `ex2_neg` (shift without net consumption fails) | `decide` | proved (negative control fails as it should) |
| same 15 rows (`#eval`, compiled) | evidence | `[true × 15]` |

This remains **evidence**. It checks one run of one machine. `table_agree` is the proof.

### Line counts (Sit.lean 661 → 1049 lines, +388)

| part | lines | estimate before |
|---|---|---|
| B1-core + `step_agree` (`window`, `applyEff`, `readTop_eq`, `eff_agree`, `stepI`, `runI`, `winC`) | ≈ 124 | B1 agreement 150–300 (total) |
| B1-T (`code`, `cell`, `sitIdx`, `tabRow`, `Good`, `cell_kc`, `decO_*`, `cell_lt`, `sitIdx_spec`, `win_sitIdx`, `res_sitIdx`, `row_cell`, `table_agree`, `tabRow_reads_lt`) | ≈ 103 | (in the 150–300) |
| `mix_sit` refactor | ≈ +10 net | — |
| B2 `run_good` (+ `table_agree_run`) | ≈ 40 | 60–120 |
| EX2 (evidence) | ≈ 106 | — |

**B1 + `run_mem_Γfin` ≈ 277 proof lines vs 210–420 estimated**, at the low end.

## Is block B done?

**Yes, with the following loose ends, none of them blocking and none inside B's statements:**

1. **C2 is essentially already proved.** P4's C2 (`cells_step`: "if all heights are `≤ H−d`, then
   `cells (step c)` is the δ-shift/fill of `cells c` given by `sitStep`") is `table_agree`, provided
   C1 adopts `Enc.cell` as its cell encoding. C1's decoding round-trip (`decodeCells`) is still open. The
   C estimate below drops accordingly, but C2 is only "done" once C1 is fixed on `Enc.cell`.
2. **The link between clause satisfaction and `tabRow` is not a B item.** `tabRow` was written to be
   "what the D3Shift clauses force" (pushed fill `[0,p)`, in-range `[p, H−max+p)`, overflow ⊥).
   Proving that a satisfying assignment's row `t+1` *equals* `tabRow` of row `t` is C6. Proving that the
   real run's rows satisfy the clauses is C5. `depth_cover`/`depth_disjoint` already match `tabRow`'s three branches.
3. **Heights.** B1-T takes heights `≤ H − d` as a hypothesis. Along a run this is A5 (`height_le`),
   in block A. It is not started.
4. **`stepI`/`runI` now exist in Sit.lean.** A3's `run` should reuse `runI`, not redefine it.
5. Cosmetic: the first example `[EX]` still uses its own local `cell`/`sitIdx`/`tabRow` (identical
   to the generic ones instantiated at `exE`). This is harmless and was left as checked evidence.

## Updated P6 estimate (supersedes the 2026-09-29 third-session table)

| Block | Estimate | Basis |
|---|---|---|
| **D total** | ≈ 6.55k–8.25k | unchanged |
| A (plumbing) | 300–500 | unmeasured; A3 simplified slightly (`runI` exists) |
| **B (locality)** | **≈ 0.74k, DONE** | measured: 0.46k (B2+B3) + ≈ 0.28k (B1 + `run_good`) |
| C (tableau semantics) | **2.8k–4.7k** (+ ≈ 0.2k reserve) | was 3.0k–5.0k. C2 is covered by `table_agree` (−0.2k to −0.3k). C5/C6 are still completely unmeasured |
| **A + B + C** | **≈ 3.85k–6.15k** | vs 4.15k–6.9k |
| **Total** | **≈ 10.4k–14.4k lines** | vs 10.7k–15.15k |

Verified lines ≈ 4.7k + 0.28k ≈ **5.0k**. Remaining ≈ 5.4k–9.4k ⇒ **≈ 6–11 sessions** at ~900
lines/session. The drop comes mostly from C2 folding into B1-T, which should be confirmed when C1 is written.

None of this touches `sat_in_p` (step (d), the open problem). **Status: NOT PROVED.**

## Checks (all run this session, output quoted)

* Lakefile diff applied (approved in the session prompt). First `lake build`: `✔ [1263/1264] Built Sit (208s)`,
  `Build completed successfully (1264 jobs).` Final `lake build` after all B1 changes:
  `✔ [1263/1264] Built Sit (51s)` / `Build completed successfully (1264 jobs).` The only warnings are the
  three known `sorry`s (Challenge.lean:3, CookLevin.lean:803, SatInP.lean:15). There are no warnings from Sit.lean.
* `#print axioms` on **all 44 new/changed declarations plus `ex_rows`** (45 lines of output): every set
  is a subset of `[propext, Classical.choice, Quot.sound]`. For example, `eff_agree`, `step_agree`, `run_good`, `good_step`,
  `good_init`, `row_cell` → `[propext, Quot.sound]`; `readTop_eq`, `window` → `[propext]`; `applyEff`
  → none; `table_agree`, `table_agree_run`, `sitIdx_spec`, `mix_sit`, `ex2_rows`, `ex2_neg` →
  `[propext, Classical.choice, Quot.sound]`. **No `sorryAx`.**
* Banned-token scan (`sorry|admit|axiom|native_decide|decide +native|implemented_by|@[extern|unsafe|
  partial|open private|set_option debug.|run_cmd|addDecl`) on Sit.lean and lakefile.toml: no matches (`grep exit: 1`).

## What carries forward vs. what is scratch

* **Carries forward (Sit.lean, root):** `eff_agree`, `step_agree`, `stepI`, `runI`, `winC`,
  `Enc.code/cell/sitIdx/tabRow/Good`, `Enc.table_agree`, `Enc.table_agree_run`, `Enc.run_good`,
  `Enc.mix_sit`. C1/C5/C6 should be stated in terms of `Enc.cell`, `Enc.code`, `Enc.sitIdx` and `runI`.
* **Evidence only:** `[EX]` and `[EX2]` sections.
* **Scratch (session scratchpad, not in the repo):** `B1.lean`, `B1T.lean`, `B1all.lean` (had a
  placeholder `sorry` for `mix_sit` during development; superseded by the proved `mix_sit` in Sit.lean),
  `ex2test.lean`, `ax.lean`.

## Lakefile

No change needed or proposed this session beyond the approved `"Sit"` root.


---

# C1: CELL ENCODING AND DECODING ROUND-TRIP (2026-09-30, stated before any code)

## The format (fixed on `Enc.cell`, no new encoding)

A tableau row of height `H` for a configuration `c` is
* the combined (label, state) code `Enc.code c = E.lc (c.l, c.var)`, in `[0, A0)`;
* the `KK·H` cell codes `Enc.cell c k j` for `k < KK`, `j < H`, where
  `Enc.cell c k j = ((c.stk (E.kd k))[j]?).elim 0 (E.enc (E.kd k))`: top-indexed (`j = 0` is the top),
  `0` = ⊥ (below the bottom of the stack), symbol `dec k i` has code `i + 1`.

Both `Enc.code` and `Enc.cell` already exist in Sit.lean (B1-T). C1 adds only the decoder and the
round-trip lemmas. P4's old phrase "`cells` / `decodeCells`" now means `Enc.code`+`Enc.cell` / `Enc.decRow`.

## Does `table_agree` already use `Enc.cell`? **Yes. No change to `table_agree` is needed.**

`Enc.table_agree` (Sit.lean) concludes
`E.code (stepI M c) = E.na (E.sitIdx c) ∧ ∀ k < E.KK, ∀ j < H, E.cell (stepI M c) k j = E.tabRow H (E.sitIdx c) (E.cell c) k j`.
Its cell encoding **is** `Enc.cell`, and `sitIdx` reads its windows from `Enc.cell` too. C1 is therefore
stated on exactly the encoding `table_agree` uses, and C2 folds in without touching an already-proved lemma.

## What "decodes correctly" means (the C1 statements)

Decoder: `Enc.decRow H n w : M.Cfg` with label/state `E.ld n` and stack `k` = the maximal run of
valid codes `w (kc k) 0, w (kc k) 1, …` (read through `decO`) before the first ⊥, cut at `H` (`decS`).

`RowOK H w` (the arrays C6 will have to produce from a satisfying assignment): for `k < KK`, `j < H`,
* validity: `w k j ≤ sz (kd k)` (code is ⊥ or a code of stack `kd k`'s own effective alphabet);
* prefix form: `w k a = 0`, `a ≤ b < H` ⇒ `w k b = 0` (no symbol below a ⊥).

| name | statement |
|---|---|
| C1a `decRow_enc` | `Good c`, all heights `≤ H` ⇒ `decRow H (code c) (cell c) = c` (full `TM2.Cfg` equality) |
| C1b `enc_decRow` | `n < A0`, `RowOK H w` ⇒ `code (decRow H n w) = n` and `cell (decRow H n w) k j = w k j` for `k < KK`, `j < H` |
| C1c `cell_rowOK` | `Good c` ⇒ `RowOK H (cell c)` (real rows are valid and prefix-form) |
| C1d `decRow_good`, `decRow_height` | a decoded row is `Good` and has heights `≤ H` |
| C1e `decRow_congr` | `decRow` depends only on the window `k < KK`, `j < H` |
| C1f `row_inj` | two good configurations with heights `≤ H`, same code and same cells on the window, are equal |
| C2' `decRow_tabRow` | **the C2 link in decoded form:** `depth M ≤ H`, `Good c`, heights `≤ H − depth M` ⇒ `decRow H (na (sitIdx c)) (tabRow H (sitIdx c) (cell c)) = stepI M c` |

C2' is how C6 will use the block: row `t` decodes to `c` (C1a/C1b) ⇒ the clauses force row `t+1` = `tabRow` of row `t` (C6's own
work) ⇒ row `t+1` decodes to `stepI M c` (C2'). C2' is a corollary of `table_agree` + C1a + C1e; if it needs
more than that, C2 did not really fold in, and that will be reported.

## C1: results (same session)

**C1 is proved, as stated above, with no change to `table_agree` or to any other existing declaration.**
It lives in Sit.lean, section `[C1]` (a root already, so no lakefile change). Every row of the statement
table above is proved under the name given there. Sit.lean grew from 1049 to 1245 lines.

### What each piece is

* `decS f j m` (generic): read `f j, f (j+1), …` for at most `m` steps, stopping at the first `none`.
  Lemmas: `decS_length`, `mem_decS`, `decS_congr`, `decS_of_list` (a list of length `≤ m` read back
  through its own `getElem?` is itself), `getElem?_decS` (on prefix-form input, cell `i` of the result
  is `f (j+i)`). All are structural recursions on `m`/the list, in the same pattern as `eff_bound`.
* `Enc.decRow H n w := ⟨(ld n).1, (ld n).2, fun k => decS (decO k ∘ w (kc k)) 0 H⟩`.
* `Enc.RowOK H w`: validity `w k j ≤ sz (kd k)` plus prefix form, for `k < KK`, `j < H`.
* C1a `decRow_enc`, C1b `enc_decRow`, C1c `cell_rowOK`, C1d `decRow_good`/`decRow_height`,
  C1e `decRow_congr`, C1f `row_inj`. Helpers: `decO_eq_none`, `enc_decO`.
* `stepI_height`: `|(stepI c).stk k| ≤ |c.stk k| + depth M` (from `step_agree` + `eff_bound`).
* **C2' `decRow_tabRow`**: `depth M ≤ H`, `Good c`, heights `≤ H − depth M` ⇒
  `decRow H (na (sitIdx c)) (tabRow H (sitIdx c) (cell c)) = stepI M c`. **Proof: 5 lines**:
  `table_agree`, then `decRow_congr`, then `decRow_enc` at `stepI c` (goodness from `good_step`, height from
  `stepI_height`). **So C2 does fold into `table_agree` as cheaply as last session's report assumed.** The only
  addition is the hypothesis `depth M ≤ H`, which `table_agree` itself does not need. It is used only to bound
  the height of the *next* row by `H`.

### Did it need new techniques? Fix rounds

No new techniques: structural recursion + `omega`, and `obtain ⟨l, v, S⟩ := c` for `Cfg` equality, as in
`step_agree`. **One fix round, two errors:**
1. In `cell_rowOK` the ⊥ case of my case split dropped `length ≤ j`, so `omega` could not close the
   prefix-form goal. I strengthened the case split.
2. `stepI_height` does not mention `E`, so `E.stepI_height` dot notation failed. I moved it out of `namespace Enc`.
   (The scratch check hid a missing `{M : FinTM2}` binder because `lake env lean` on a scratch file does not
   apply the package's `autoImplicit = false`. I made the binder explicit before integrating. `lake build` then
   compiled it with the package options.)

### A consequence for C6 (paper observation, not a Lean lemma)

C6's induction does **not** need to decode interior rows. Its natural invariant is "row `t` of the assignment
**equals** `(code, cells)` of `runI t`". Given that, row `t+1` = `tabRow` of row `t` (the clause-forcing part,
C6's real work) = `cells (runI (t+1))` by `table_agree_run`. `RowOK` is then inherited automatically through
`cell_rowOK`. Decoding (`decRow`, C1b) is needed only
* at **row 0**: the init family must force `RowOK` there. Validity needs the "invalid codes excluded at
  row 0" item, which is still open. Prefix form is a **new explicit obligation of the init/input-decoder
  family**: no symbol below a ⊥ on any stack at row 0;
* at the **certificate**: reading `y` back out of row 0.

This moves no estimate. It does mean the scariest-sounding part of C6 ("decoded rows are the real run") reduces
to one clause-forcing lemma, "a satisfying row `t+1` equals `tabRow` of row `t`", plus `table_agree_run`.

### Line count (fresh data point: C1 was not separately budgeted)

| part | lines (incl. docstrings/blank) | non-blank, non-comment |
|---|---|---|
| generic `decS` + 5 lemmas | 73 | |
| `stepI_height` | 14 | |
| `Enc` part (`decRow`, `RowOK`, C1a–C1f, helpers, C2') | 107 | |
| **C1 total** | **194** | **152** |

Comparison with block B: B1 + `run_mem_Γfin` was ≈ 277 lines against 210–420 estimated, and B2+B3 ≈ 455. C1 at
≈ 0.19k is in line with P4's rating "M" and with block B's per-lemma cost. It needed one fix round, like B1.

### Is this the first sign that C is harder than 2.8k–4.7k? **No, but it is not evidence that C is cheap either.**

C1 is the same kind of work as block B: structural facts about lists and encodings of *one* configuration.
It says nothing about the part of C that has not been measured. That part is **clause semantics**: relating a
Boolean assignment over `xIdx H t a` variables and the D3 families' generated clause lists (D3Fam/D3Shift/D3SDef,
dense CNF) to `tabRow`/`na`. That is C5 (the real run satisfies every clause) and C6 (clauses force row `t+1` =
`tabRow` row `t`). No lemma so far touches an assignment. The C5/C6 risk is exactly as unmeasured as before. The honest
reading of this session is "C1 did not add cost". It is not "C is cheaper than thought".

### Updated P6 estimate (supersedes the B1 session's table)

| Block | Estimate | Basis |
|---|---|---|
| **D total** | ≈ 6.55k–8.25k | unchanged |
| A (plumbing) | 300–500 | unmeasured |
| **B (locality)** | ≈ 0.74k, DONE | measured |
| C (tableau semantics) | **2.8k–4.7k** (+ ≈ 0.2k reserve), of which **C1 + C2 ≈ 0.19k DONE** | C1 measured at 0.19k and C2 confirmed as a corollary. C5/C6 are unmeasured, so the band is left as it was: C1 was not budgeted separately, and I will not shrink the band on a cheap plumbing lemma |
| **A + B + C** | ≈ 3.85k–6.15k | unchanged |
| **Total** | **≈ 10.4k–14.4k lines** | unchanged |

Verified lines ≈ 5.0k + 0.19k ≈ **5.2k**. Remaining ≈ 5.2k–9.2k ⇒ **≈ 6–10 sessions** at ~900 lines/session.

None of this touches `sat_in_p` (step (d), the open problem). **Status: NOT PROVED.**

### Checks (run this session, output quoted)

* Scratch check `lake env lean C1.lean` (imports built `Sit`): first run 2 errors (above), second run no output.
* `lake build` after integrating into Sit.lean: `✔ [1263/1264] Built Sit (52s)` /
  `Build completed successfully (1264 jobs).` The only warnings are the three known `sorry`s (Challenge.lean:3,
  CookLevin.lean:803, SatInP.lean:15). Sit.lean produces no warnings.
* `#print axioms` on all 19 new declarations (+ `table_agree`): every set ⊆ `[propext, Classical.choice, Quot.sound]`.
  `decS` → none; `mem_decS` → `[propext]`; `decS_congr`, `decRow`, `RowOK`, `decRow_good`, `decRow_congr` →
  `[propext, Quot.sound]`; the rest (incl. `decRow_enc`, `enc_decRow`, `cell_rowOK`, `row_inj`, `decRow_tabRow`) →
  `[propext, Classical.choice, Quot.sound]`. **No `sorryAx`.**
* Banned-token scan on Sit.lean and lakefile.toml: no matches (`grep exit: 1`).

### Lakefile

No change needed or proposed. C1 went into Sit.lean, which is already a root.

---

# C6, FIRST CLAUSE-FORCING LEMMA: IN-RANGE SHIFTS (2026-09-30, third) — target written BEFORE any proof

## Lakefile

No change planned. The lemma goes into Sit.lean (a root) as a new section `[C6]`. It is checked first as a scratch
file that imports the built `Sit`.

## What "satisfying assignment" means here (the formal objects)

* Assignment: `a : List Bool`, exactly as in `SATDef.SAT w := ∃ a, cnfSat (decodeCNF w) a`.
  Variable `v` is **true** iff `a[v]? = some true`. New abbreviation: `Tr a v : Prop := a[v]? = some true`.
  (Indices `≥ a.length` are neither true nor false and satisfy no literal. That is the existing `clauseSat` semantics,
  not a new convention.)
* Clause satisfaction is the existing `SATDef.clauseSat`: `∃ j b, c[j]? = some (some b) ∧ a[j]? = some b`.
  `cnfSat φ a := ∀ c ∈ φ, clauseSat c a`.
* The formula is the D3Shift family **itself**: hypothesis `cnfSat (D3SH.shFamily L sa pl cn pu N T H) a`.
  The final reduction outputs `encodeCNF` of a concatenation of families. `decodeCNF ∘ encodeCNF = id`
  (`decodeCNF_encodeCNF`, CookLevin.lean) and `cnfSat (φ ++ ψ)` gives both halves. Both are block-A plumbing, not
  this lemma.

## The target, in three layers

**L0 (generic, dense clauses).** `clauseSat (denseClause V ls) a → ∃ p b, (p, b) ∈ ls ∧ a[p]? = some b`.
Distinct positions are not needed, because only membership is used.

**L1 `sh_force` (pure clause forcing, the D3Shift parameters, no machine).** If `cnfSat (shFamily L sa pl cn pu N T H) a`,
`t < T`, `i < N`, `k < KK`, `u < H − max (pl i k) (cn i k)`, `x < g`,
`Tr a (xIdx H (t+1) (sa i))` (that is, `S[t,i]`) and `Tr a (cIdx H t k (u + cn i k) x)`,
then `Tr a (cIdx H (t+1) k (u + pl i k) x)`.

**L2 `sh_step_cell` (invariant form, a real `M` with `E : Enc M`, layout `E.layout`).**
Row predicate (**no decoding**): `CellsAre a H t w := ∀ k < KK, ∀ j < H, ∀ x < g, Tr a (cIdx H t k j x) ↔ x = w k j`
("row `t`'s cell block is exactly the one-hot image of the array `w`").
Hypotheses:
* `cnfSat (shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a`, `t < T`;
* `Good c` and `CellsAre a H t (E.cell c)` (**the invariant at `t`**);
* `Tr a S[t, sitIdx c]` (the situation variable of `c`'s own situation);
* at-most-one at the target cell of row `t+1`: `∀ x y < g, Tr a C[t+1,k,j,x] → Tr a C[t+1,k,j,y] → x = y`;
* `k < KK` and `j` in range: `pl i k ≤ j < H − max (pl i k) (cn i k) + pl i k` (with `i = sitIdx c`).
Conclusion: `∀ x < g, Tr a (cIdx H (t+1) k j x) ↔ x = E.tabRow H (sitIdx c) (E.cell c) k j`.

**L3 `sh_step_run` (link to the real run: the invariant is propagated on in-range depths).** For
`c = runI M (initList M s) t` with heights `≤ H − depth M`, L2's hypotheses give
`∀ x < g, Tr a (cIdx H (t+1) k j x) ↔ x = E.cell (runI M (initList M s) (t+1)) k j` for in-range `j`.
This is L2 + `table_agree_run`. It is the direct test of the invariant idea: it should need **no** `decRow`, no
`RowOK`, and no decoding of row `t` or `t+1`.

## What is deliberately a hypothesis (so the gap stays visible)

* `S[t, sitIdx c]` true. The S-definition family (D3SDef = D3Fam instance) will force it from
  `CellsAre` + the code block at row `t` + `sitIdx_spec`. That is a different clause family, so it is not this session.
* At-most-one at row `t+1`. It will come from the cell one-hot family (D3OneHot). Also a different family.
* The overflow and pushed-fill depths. These are the other two clause kinds of `shFamily`. They are not this session.

## Success criterion for the invariant idea (fixed now)

"Worked as hoped" means L3 is proved from L2 and `table_agree_run` by rewriting alone, and no row is decoded. If L2 or L3 needs
`decRow`/`enc_decRow`/`RowOK`, or a new statement about decoded configurations, it is reported as "needed real row decoding".

## Outcome: L0–L3 proved exactly as stated above, plus a positive variant (L2⁺/L3⁺) the proof exposed

Everything is in Sit.lean, section `[C6]` (`section C6 … end C6`, after `[C1]`). Sit.lean grew from 1245 to 1389 lines. No lakefile change.

| name | layer | statement (as proved) |
|---|---|---|
| `Tr a v` | def | `a[v]? = some true` |
| `mem_of_lookup`, `clauseSat_dense` | L0 | `clauseSat (denseClause V ls) a → ∃ p b, (p,b) ∈ ls ∧ a[p]? = some b` |
| `sh_force` | L1 | the target L1, verbatim (general `L sa pl cn pu`, no machine) |
| `Enc.CellsAre`, `Enc.CellsHold` | defs | exact one-hot image of `w` in row `t` / positive form `∀ k<KK, j<H, Tr a C[t,k,j,w k j]` |
| `Enc.sh_hold` | L2⁺ (core) | `CellsHold a H t (cell c)`, `Good c`, `S[t,sitIdx c]`, in-range `j` ⇒ `Tr a C[t+1,k,j,tabRow …]`. **No at-most-one** |
| `Enc.sh_step_cell` | L2 | the target L2, verbatim (with at-most-one at `(t+1,k,j)`); proof = `sh_hold` + `hamo` |
| `Enc.sh_step_run` | L3 | the target L3, verbatim; proof = `rw [table_agree_run …]` + `sh_step_cell` (2 lines) |
| `Enc.sh_step_run_pos` | L3⁺ | L3 with `CellsHold` instead of `CellsAre` and no `hamo`; conclusion `Tr a C[t+1,k,j, cell (runI (t+1)) k j]` |

**Fix rounds: zero.** The first scratch compile of L0–L3 produced no errors. The refactor that added L2⁺/L3⁺ also compiled
first time under `lake build`. The only earlier error was in a 1-lemma skeleton I compiled to probe a rewrite name
(`getElem?_range'` vs `getElem?_range`), before the real attempt.

## Did the invariant idea work? **Yes, as hoped, for this family. No modification, no row decoding.**

Against the criterion fixed before the proof:
* L3 is `table_agree_run` + L2 by one `rw` and one `exact`. It uses no `decRow`, `enc_decRow` or `RowOK`, and makes no
  statement about decoded configurations.
* L2 needs from row `t` only `Good c` (from `run_good`), `cell_lt`, `sitIdx_spec.1` (`i < N`), and the literal of one
  real cell. `tabRow` is unfolded once in the in-range case.
* So the real content of "clauses force row `t+1` from row `t`" for this family is L1: a membership proof into the
  generated `flatMap` list plus a 3-way case split on the literal. It is ~20 lines.

**Something the proof showed that the paper note did not have.** Row `t` is only ever used positively: the literal of the
real cell is true. Exactness (`CellsAre`'s `→` direction) is needed only because the target *states* exactness at
`t+1`, and that is what at-most-one supplies. L3⁺ proves that the **positive invariant** `CellsHold` propagates
through in-range depths with **no one-hot hypothesis at all**. On paper (not proved), the other consumers are:
* the S-definition clause (`¬X ∨ ⋁¬C ∨ S`, D3Fam shape) and the update clause (same shape, head `X[t+1,na i]`)
  need only positive facts at row `t`;
* overflow and pushed fill do not read row `t` at all.

So the C6 induction can plausibly carry the weaker invariant "the real code/cell literals of `runI t` are true". Then
**one-hot semantics would be needed only at the endpoints**: at row 0 to extract the certificate, and at row `T`
(at-most-one on the code block) to conclude that the accept literal belongs to `runI T`. This is a **claim to test**
in the S-def / assembly sessions, not a result. It does not change which families must be *generated* (the one-hot family
stays, over all rows), only which semantic lemmas C6 must prove about it.

## Nothing required real row decoding, so item 3 of the request does not trigger

Decoding is still needed at row 0 and at the certificate, exactly as in last session's note. Nothing in this lemma moved
decoding into the step.

## Line count (fresh data point, no prior budget)

| part | lines incl. docstrings/blank | non-blank, non-comment |
|---|---|---|
| section header + `open` | 7 | 2 |
| L0 generic (`Tr`, `mem_of_lookup`, `clauseSat_dense`) | 27 | 22 |
| L1 `sh_force` | 23 | 20 |
| defs `CellsAre`/`CellsHold` + L2⁺ `sh_hold` | 30 | 21 |
| L2 `sh_step_cell` | 20 | 16 |
| L3 `sh_step_run` | 17 | 14 |
| L3⁺ `sh_step_run_pos` | 17 | 13 |
| **total `[C6]` section** | **141** | **108** |

Reference points:
* **C1: 194 lines, 1 fix round.** This lemma is about 0.7× C1, with 0 fix rounds.
* **D families: 600–1000 lines each.** This lemma is about 0.15–0.25× a D family. The work is of a different kind: forcing
  reads a *spec* list (`shFamily`) and never touches the generator machine. That is why it is cheap. The expensive part
  of D (machine runs and time bounds) has no counterpart here.
* The genuinely per-family part is L1 (~23 lines). L0 (27) is reused by every family. L2/L3 are the Enc-level wrappers.
  The in-range kind is the one clause kind of `shFamily` that reads row `t`, so the other two kinds should cost less than
  L1 each.

## Item 5: what this says about the init family's row-0 obligation (now a known dependency)

The induction's base case needs, at row 0, the invariant for a configuration of the form `initList M s`: `CellsHold a H 0
(cell (initList M s))` (plus the code literal), or `CellsAre` if exactness is kept. The certificate is chosen **by
the assignment**, so `s` must be constructed from `a`. That fixes the shape of the init family's semantic lemma:

1. **State it as `∃ s, (the row-0 invariant for initList M s) ∧ |s| ≤ ℓ`, not via `decRow`.** `decRow`/`enc_decRow`/`RowOK`
   are the *means* of building `s` inside that lemma: read the array `w` at row 0 with one-hot, show `RowOK H w`, and set
   `s := (decRow H n w).stk k₀`. They are not part of the interface the induction consumes.
2. **Validity** (codes `≤ sz`) is needed, because an invalid code has no `s` with `cell (initList s) = w`. This is the
   known open item "invalid codes excluded at row 0". **Prefix form** is needed for the same reason. Both are needed on
   stack `k₀` only. On the other stacks the init family must force ⊥ everywhere, which gives prefix form for free.
3. **New and concrete: a length bound on `s` must be forced by clauses.** L3 needs `hh`: heights of `runI t ≤ H − depth M`.
   On the real run this comes from `|s| + t·depth M`. `s` is chosen by the assignment, so a bound `|s| ≤ ℓ` cannot come
   from the run. It has to come from the init family forcing ⊥ at row 0, stack `k₀`, depths `j ≥ ℓ`. Then `H` must satisfy
   `ℓ + (T+1)·depth M ≤ H`. P2's `H` must be checked against this when the init family is specified. It is presumably
   already of this form (input + certificate bound + time), but it is now an explicit constraint, not an assumption.
4. At-most-one at row 0 is needed to make `w` a function of `a` (or at-least-one + a choice, if the positive invariant is
   used). Either way, **row 0 is where the one-hot semantics must be proved**.

## Updated P6 estimate (supersedes the C1 session's table)

| Block | Estimate | Basis |
|---|---|---|
| **D total** | ≈ 6.55k–8.25k | unchanged |
| A (plumbing) | 300–500 | unmeasured |
| **B (locality)** | ≈ 0.74k, DONE | measured |
| C (tableau semantics) | **2.8k–4.7k** (+ ≈ 0.2k reserve), of which C1+C2 ≈ 0.19k and **the first C6 forcing lemma ≈ 0.14k DONE** | see below |
| **A + B + C** | ≈ 3.85k–6.15k | unchanged |
| **Total** | **≈ 10.4k–14.4k lines** | unchanged |

Why the C band is **not** narrowed on this measurement:
* **For C6 (soundness) this is evidence of cheapness.** The per-clause-kind forcing cost is ~20–25 lines plus wrappers.
  A plausible C6 total is then: forcing for S-def/update ~60–150 (D3Fam's `litPos` uses `/`/`%` over `KK·d` window
  literals, so its membership and literal case split is heavier than `shLits`' 3-element list), overflow + pushed fill
  ~40–60, row assembly via `depth_cover` ~40–80, induction ~50–100, accept at row `T` ~50. That is ≈ 0.3k–0.5k beyond
  what exists now. The init/row-0 lemma is not counted here: its family is unbuilt, and it will carry the decoding.
* **C5 (completeness) is still unmeasured, and this session exposed two costs specific to it that C6 does not pay:**
  1. The reverse of L0: from a true literal to `clauseSat`. This needs `(denseClause V ls)[p]? = some (some b)`, i.e.
     `ls.lookup p = some b`. That holds only if `p`'s first occurrence in `ls` carries `b`. So C5 needs **distinct
     positions** in every literal list. D3Fam's `Inc`/`Mono` sortedness proofs may be reusable for this, but that is
     unchecked.
  2. Building the witness `a : List Bool` of length `numVars` with `a[v]` defined by cases on `v`'s decoded
     `(t, a)`/`(t,k,j,x)` requires **index inversion** of `xIdx`/`cIdx` (div/mod over `rowW`). No lemma so far does
     this.

  So one side of C got cheaper-looking and the other gained named costs. I am not moving the band on one ~0.14k data
  point. If the S-def forcing lemma also comes in near L1's size, the C6 part of the band can be tightened then.

Verified lines ≈ 5.2k + 0.14k ≈ **5.35k**. Remaining ≈ 5.05k–9.05k ⇒ **≈ 6–10 sessions** at ~900 lines/session (unchanged).

None of this touches `sat_in_p` (step (d), the open problem). **Status: NOT PROVED.**

## Checks (run this session, output quoted)

* Scratch `lake env lean C6.lean` (imports built `Sit`): no errors on the first full attempt. The `#print axioms` output
  there matched the output below.
* `lake build` after integrating (final version, with L2⁺/L3⁺): `Build completed successfully (1264 jobs).` The only
  warnings are the three known `declaration uses 'sorry'` (Challenge.lean:3, CookLevin.lean:803, SatInP.lean:15).
* `#print axioms` (against the built `Sit`):
  `Tr` → `[propext]`; `CellsAre`, `CellsHold` → `[propext, Quot.sound]`; `mem_of_lookup`, `clauseSat_dense`,
  `sh_force`, `sh_hold`, `sh_step_cell`, `sh_step_run`, `sh_step_run_pos` → `[propext, Classical.choice, Quot.sound]`.
  **No `sorryAx`.**
* Banned-token scan on Sit.lean and lakefile.toml: no matches (`grep exit: 1`).

## Lakefile

No change needed or proposed.

---

# C6, SECOND CLAUSE-FORCING LEMMA: S-DEFINITION (2026-09-30, fourth) — target written BEFORE any proof

## Lakefile

No change planned. The lemmas go into Sit.lean section `[C6]`. Sit does not import D3SDef (not a root), and none is
needed: the S-definition family is *literally* `D3Fam.family L la sa wa` with `na := sa` (`D3SD.sdFamily_eq`, proved in
D3SDef). So the forcing lemma is stated on `D3Fam.family`, whose clause literals are exactly the `litPos` list with the
`(j-1)/d`, `(j-1)%d` window indexing. It therefore covers the S-definition clauses (`na := sa`) and, unchanged, the
update clauses (`na := na`, not this session).

## The target, in layers (same structure as the shift family)

**L0** `clauseSat_dense`: reused from the shift session, unchanged.

**L1 `fam_force` (pure clause forcing, D3Fam parameters, no machine).** If `cnfSat (D3Fam.family L la na wa T H N) a`,
`t < T`, `i < N`, `Tr a (xIdx H t (la i))` and
`∀ n < KK·d, Tr a (cIdx H t (n/d) (n%d) (wa i (n/d) (n%d)))` (the window literals, indexed by the same div/mod as
`litPos`), then `Tr a (xIdx H (t+1) (na i))`. A `(k,j)`-form corollary with `k < KK, j < d` is also wanted, because
that is how `Enc`'s tables are stated (`sitIdx_spec`).

**L2 `Enc.sd_hold` (invariant form, `E : Enc M`, layout `E.layout`, family with `na := E.sa`).**
Row predicate, positive and undecoded: `CellsHold a H t (E.cell c)` (existing) plus the new
`CodeHolds a H t c := Tr a (xIdx H t (E.code c))`. Hypotheses: `Good c`, `depth M ≤ H`, `t < T`.
Conclusion: `Tr a (xIdx H (t+1) (E.sa (E.sitIdx c)))`, i.e. `S[t, sitIdx c]`, exactly the hypothesis `hS` of
`sh_hold`. Uses `sitIdx_spec` (`i < N`, `la i = code c`, `wa i k j = cell c k j` for `k<KK, j<d`).

**L3 `Enc.sd_step_run`.** Same for `c = runI M (initList M s) t`. Then `sd_step_run` composes with
`sh_step_run_pos` (hS discharged) — no new hypothesis beyond the row-`t` positive invariant.

## What "worked as hoped" means here (fixed now)

* **Yes** iff L2 and L3 need only positive facts about row `t`: the code literal and the real-cell literals for depths
  `j < depth M`. No at-most-one, no at-least-one, no `CellsAre`, no `decRow`/`RowOK`, no exactness of the code block.
  L1 must go through with the div/mod indexing handled *inside* the proof, not by assuming a pre-flattened `(k,j)` list.
* **No (needs one-hot)** iff some step needs a "false" literal fact, e.g. to rule out a wrong window value, or exactness
  of the code block. Then it is reported plainly, together with which families this implies need it.
* "Compiled clean" = zero fix rounds on the first scratch compile of L1–L3. Any fix round is counted and reported.
* New observation to check, not assumed: the S-definition clause reads the window at depths `j < d` only, but the
  shift/pushed-fill clauses populate row `t+1`'s window from *two* clause kinds (pushed fill `j < pl`, in-range `j ≥ pl`).
  So the positive invariant at row `t+1` needs both kinds to cover `[0, d)`; that assembly is not this session
  (`depth_cover`), but L2's hypothesis will make the dependency explicit.

## Outcome: L1–L3 proved as stated, plus a composition lemma; zero fix rounds; positive-only invariant held

Everything is in Sit.lean, section `[C6]` (after the shift lemmas, before `end C6`). Sit.lean grew from 1389 to 1479 lines.
No lakefile change. `lake build`: 1264 jobs, clean (only the pre-existing `sorry` warnings in Challenge/CookLevin/SatInP).

| name | layer | statement (as proved) |
|---|---|---|
| `fam_force` | L1 | `cnfSat (D3Fam.family L la na wa T H N) a`, `t<T`, `i<N`, `Tr X[t,la i]`, `∀ n < KK·d, Tr C[t,n/d,n%d,wa i (n/d) (n%d)]` ⇒ `Tr X[t+1,na i]` (general, no machine) |
| `fam_force_kj` | L1 | same with `∀ k<KK, ∀ j<d` hypotheses (3-line corollary: `n/d<KK`, `n%d<d`) |
| `Enc.CodeHolds` | def | `Tr a (xIdx H t (E.code c))` |
| `Enc.sd_hold` | L2 | `Good c`, `depth M ≤ H`, `CodeHolds`, `CellsHold a H t (cell c)` ⇒ `Tr a S[t, sitIdx c]` (family with `na := E.sa`) |
| `Enc.sd_step_run` | L3 | same for `c = runI M (initList M s) t` (one term) |
| `Enc.sdsh_step_run_pos` | L3+shift | composes with `sh_step_run_pos`: positive row-`t` invariant (code + cells) ⇒ in-range cells of row `t+1`; `hS` is no longer a hypothesis |

`#print axioms`: `fam_force`, `fam_force_kj`, `sd_hold`, `sd_step_run`, `sdsh_step_run_pos` all depend on exactly
`[propext, Classical.choice, Quot.sound]`; `CodeHolds` (a def) on `[propext, Quot.sound]`. Banned-token scan of Sit, D3Fam, D3OneHot,
D3Shift, Prog, D3SDef: no matches.

## Verdict against the criterion fixed before the proof

**Worked as hoped. The positive-only invariant sufficed. No one-hot fact was needed. No `CellsAre`, no exactness of the code
block, no `decRow`/`RowOK`.** L2 uses: `Good c`, `sitIdx_spec` (three facts: `i<N`, `la i = code c`, `wa i k j = cell c k j`),
`CodeHolds`, and `CellsHold` at depths `j < depth M`. First scratch compile of L1–L3 + composition produced no output (no
errors, no warnings); zero fix rounds. Inserting into Sit.lean and `lake build` also needed no change.

Where the div/mod indexing actually went (so this is not overstated):
* It was handled **inside the proof** of `fam_force`: membership gives `j < nLits`, a 3-way split (`j=0`, `1≤j≤KK·d`, `j=KK·d+1`), and in the middle
  case `litPos` unfolds to `cIdx ((j-1)/d) ((j-1)%d) …`, which is *literally* the instance `n := j-1` of the hypothesis. `omega` closes the
  side conditions. No lemma about `/`, `%` was needed. The forcing direction only ever uses *membership* of a literal, so it never needs
  the positions to be distinct or `xIdx`/`cIdx` to be injective.
* The div/mod cost that does exist was paid earlier, in D3SDef (`flatMap_range_divmod`, `sdLits_eq`, ~35 lines), when the S-definition
  family was shown to be `D3Fam.family` with `na := sa`. Stating the forcing lemma on `sdFamily`'s flatMap form would have avoided
  div/mod entirely, but only because that bridge was already proved. I stated it on `D3Fam.family` (the form the generator emits), which
  is the harder and honest test.
* Only `fam_force_kj` needs `n/d < KK` and `n%d < d`; that is 3 lines.

## Item 3: no asymmetry found; what it implies

No family so far needs one-hot. Shift and S-definition both read row `t` positively. Per family, on paper (not proved):
* update (`X[t+1, na i]`): same clause shape as S-def. `fam_force` applies **verbatim** with `na := E.na`; the new work is only the
  Enc-level fact `na (sitIdx c) = code (stepI c)` (a `table_agree`/`res_sitIdx` consequence).
* overflow, pushed fill: read `S[t,i]` only (row `t+1`'s situation block), never row `t`'s cells; no one-hot.
* So the conjecture stands, now supported by two clause kinds plus the shared L1: one-hot semantics is needed only at row 0 (extract `s`)
  and row `T` (accept). The at-most-one/at-least-one *families* still must be generated for those two endpoints.

Dependency the proof makes explicit (not proved here): `sd_hold` needs `CellsHold` at **all** depths `j < d` of row `t`, and the code
literal at row `t`. For `t ≥ 1` these come from row `t-1`'s clauses through three kinds: pushed fill (`j < pl`), in-range
shift (`pl ≤ j < H-max+pl`), and update (code). The window `j < d` lies in the union of the first two provided
`H ≥ d + max(pl,cn) - pl`; `H ≥ 2d` suffices. That `depth_cover` assembly is the next C6 piece, and it puts one more
constraint on P2's `H`, beside `ℓ + (T+1)·d ≤ H`. Cells with `j ≥ length` are ⊥ (code 0) in `cell`; those are also *positive*
literals (the ⊥ literal is true), so padding does not need a negative fact either.

## Line count

| part | lines (incl. docstrings/blank) |
|---|---|
| `fam_force` (L1, div/mod inside) | 32 |
| `fam_force_kj` | 9 |
| `CodeHolds` + `sd_hold` (L2) | 17 |
| `sd_step_run` (L3) | 7 |
| `sdsh_step_run_pos` (composition) | 15 |
| **total inserted (incl. section comment/namespace/blank)** | **90** (74 non-blank) |

* vs shift reference (141 lines, 108 non-blank): **0.64×** (0.69× non-blank). Cheaper even though the D3Fam literal list is the "heavier"
  indexing, because L1 is one reusable lemma and there is no per-case `hamo` layer. Without the composition lemma (15) and `fam_force_kj` (9)
  the core is ~66 lines, ≈ 0.47× shift.
* vs the C6 projection (S-def/update forcing 60–150): 90 for S-def alone; update forcing now projected at ~10–30 more (reuse of `fam_force`).
* Running C6 total: shift 141 + S-def 90 = **231**. Remaining (projected): update 10–30, overflow + pushed fill 40–60, `depth_cover` assembly
  40–80, induction 50–100, accept at row `T` ~50 → **0.19k–0.32k more**, so C6 ≈ **0.42k–0.55k** without init. The old projection was
  0.3k–0.5k beyond the first lemma, i.e. 0.44k–0.64k in total. The two data points agree (0 fix rounds, 0.09k–0.14k each); the top of the C6 band comes down.

## Item 5: what this clarifies about the two C5 costs (no C5 attempted)

1. **Distinct literal positions.** Better than feared. `D3Fam.lits_inc` (strictly increasing positions, `Inc 0 (lits …)`) already exists and
   covers exactly this list (S-def and update, under `WF`). What C5 still lacks is a generic lemma
   `Inc lo ls V → (p,b) ∈ ls → ls.lookup p = some b`; `Inc.lookup_none` is the only lookup fact now. Estimate 10–20 lines, reusable by every
   family with an `Inc` proof. Whether the shift/one-hot families' `Inc` proofs have the same shape is unchecked.
2. **`xIdx`/`cIdx` inversion.** **This lemma does not touch it.** Forcing uses the index functions only as opaque values inside
   membership; nothing is injective or inverted. That is a real C6/C5 asymmetry: C6 never needs inversion, C5 must. Cost unchanged and
   unmeasured. Whether a witness defined by forward maps avoids inversion is a C5 question, not answered here.

## Updated P6 estimate (supersedes the previous C6 table)

| Block | Estimate | Basis |
|---|---|---|
| **D total** | ≈ 6.55k–8.25k | unchanged |
| A (plumbing) | 300–500 | unmeasured |
| **B** | ≈ 0.74k, DONE | measured |
| C (tableau semantics) | **2.8k–4.7k** unchanged; C1+C2 ≈ 0.19k done; **C6 forcing 0.23k done (shift 0.14k + S-def 0.09k)** | |
| C6 sub-band (excluding init) | **0.42k–0.55k** (was 0.44k–0.64k) | two families agree: 0.09k–0.14k each, 0 fix rounds |
| **A + B + C** | ≈ 3.85k–6.15k | unchanged |
| **Total** | **≈ 10.4k–14.4k lines** | unchanged (the ~0.1k C6 shave sits inside the C reserve; not claimed) |

The C band as a whole is not narrowed: C6 is a small part; C5, C3/C4 assembly and init are unmeasured and dominate the uncertainty. Both C6
lemmas are the *easy direction* (forward use of a satisfied clause); nothing here says the same about C5.

Lakefile: no change proposed. Not started: update forcing, overflow, pushed-fill forcing, `depth_cover` assembly, C5.


# C6, SECOND SESSION: UPDATE, PUSHED-FILL AND OVERFLOW FORCING (2026-09-30, fifth session)

## Targets and success criteria (written BEFORE any proof)

Setting: `Enc.layout` families. Update = `D3Fam.family E.layout E.la E.na E.wa T H E.N`. Pushed fill / overflow = the 2nd and 3rd
clause kinds inside `D3SH.shBlk` (same `shFamily` as the in-range shift). `Tr a v := a[v]? = some true`.

**U. Update forcing (`upd_hold`, `upd_step_run`).** Statement: `Good c`, `depth M <= H`, `CodeHolds a H t c`, `CellsHold a H t (cell c)`
give `Tr a (xIdx H (t+1) (na (sitIdx c)))`; run form (with the height hypothesis `hh`) gives `CodeHolds a H (t+1) (runI (t+1))`, via
`table_agree_run.2.2.2.1`. *Expected:* near-free, because `fam_force_kj` is stated for any `(la, na, wa)`, so it is used verbatim with
`na := E.na`, and `sd_hold` is the same proof with `E.sa` in place of `E.na`. *Success:* <= ~30 lines, no new indexing lemma, no
one-hot, zero fix rounds. *Would count as NOT free:* any new div/mod lemma, or any new hypothesis beyond `hh` (needed only for
`na (sitIdx c) = code (stepI c)`).

**P. Pushed-fill forcing (`pf_force`, `pf_hold`, `pf_step_run`).** Clause: `not S[t,i] or C[t+1,k,j,pu i k j]`, `j < pl i k`.
It never reads row `t`, so the shift/S-def invariant shape ("row `t` literals hold => row `t+1` literals hold") does NOT port
literally. What "positive-only holds" means here: the *only* hypothesis about the assignment is the single situation literal
`Tr a S[t,i]` (which is itself produced from row `t` by S-def, already proved), and the conclusion is the positive literal of the
real cell `cell (runI (t+1)) k j` for `j < pl`. So the row-`t` invariant `CellsHold` is *not* an input of this lemma, and the composed
statement (S-def then pushed fill) needs `CodeHolds` + `CellsHold` at row `t` only through `sd_step_run`. Verdict rule: if the proof
is "membership of the clause, `clauseSat_dense`, kill the negative literal with `hS`" (no cell literal of row `t`, no at-most-one,
no `pu` validity beyond `tabRow` equality), the positive-only pattern held. If it needs `pu_valid`/`decO`, an at-most-one fact on
`S`, or anything about how `S` was set, that is a genuinely different argument and will be reported as such.

**O. Overflow forcing (`ov_force`, `ov_hold`, `ov_step_run`).** Clause: `not S[t,i] or C[t+1,k,H-cn+pl+r,bottom]`, `r < cn - pl`.
Same shape as P, and additionally the target literal is the code-0 (bottom) literal, so the extra obligation is arithmetic:
`tabRow = 0` at depth `H - cn + pl + r` (else-branch of `tabRow`). Success = same as P plus that one `omega`-level fact.

Cross-checks required by the task: (4) P2's `H` against the two logged constraints, done directly (see the results section); (5) line
counts against the 0.09k-0.14k per-family reference; (7) `#print axioms` for every new declaration, banned-token scan, `lake build`.

Not started this session (as instructed): row assembly, induction, accept, init, C5.


## Results (same session, against the criteria above)

Inserted in `Sit.lean` section [C6] (Sit 1479 -> 1609 lines, +130 including header/namespaces/blanks; `lake build` clean, 1264 jobs, only the
three pre-existing `sorry` warnings in Challenge/CookLevin/SatInP). New declarations, each `#print axioms` = `[propext, Classical.choice, Quot.sound]`:
`Enc.upd_hold`, `Enc.upd_step_run`, `pf_force`, `ov_force`, `Enc.pf_hold`, `Enc.ov_hold`, `Enc.pf_step_run`, `Enc.ov_step_run`.
Banned-token scan of Sit.lean: no hits. Fix rounds for the proofs: 0 (the first scratch compile failed only because my scratch header
lacked `open Turing Function`; proof bodies were unchanged afterwards).

**U. Update: as free as expected.** `upd_hold` is `sd_hold` with `E.na` for `E.sa`, character-for-character the same proof (`fam_force_kj`
verbatim). `upd_step_run` adds one `rw` with `table_agree_run.2.2.2.1` (`code (runI (t+1)) = na (sitIdx c)`), which is where the height
hypothesis `hh` enters. No new indexing lemma, no one-hot. ~29 lines including wrapper.

**P. Pushed fill: pattern held, no rework.** `pf_force` needs only clause membership (third `shBlk` component), `clauseSat_dense`, and
`hS` to kill the negative literal; two-case `rcases`. `pf_hold` is `tabRow = pu` (`if_pos`) plus `pf_force`. Nothing about row `t` cells,
no at-most-one, no `pu_valid`. The invariant *shape* did differ, as predicted: the hypothesis list has `hS` and no `CellsHold`/`CodeHolds`.
That is a simplification, not a different argument. `pf_step_run` needs `depth M <= H` only to get `j < H` for the `table_agree_run` cell equality.
~39 lines for the three layers.

**O. Overflow: pattern held; one extra arithmetic layer, no new idea.** `ov_force` is `pf_force` with the second `shBlk` component and the
bottom literal. `ov_hold` needs: `tabRow = 0` on `j >= H - max pl cn + pl` (two `if_neg` by `omega`), and the reindexing `r := j - (H - cn + pl)`,
where `r < cn - pl` uses `pl, cn <= depth M <= H` (from `pl_le`, `cn_le`, `hdH`) to avoid truncated subtraction. The lemma is stated for the whole
else-region `[H - max pl cn + pl, H)`, so it also covers the `cn <= pl` case vacuously (region empty). ~52 lines for the three layers.

**Do all four families agree? Yes on cost class and invariant style; the only asymmetry is in what they consume.** Shift and update/S-def read row `t`
(`CellsHold`, plus `CodeHolds`); pushed fill and overflow read only `S[t+1 block]`, and S itself comes from S-def (already proved), so
the row-`t` invariant reaches them only through `sd_step_run`. No family needed one-hot. Not tested: nothing here says anything about C5 (completeness).

## Line counts vs the 0.09k-0.14k reference

| lemma | lines (all layers) | vs reference |
|---|---|---|
| shift (previous) | 141 | 0.14k |
| S-def (previous) | 90 | 0.09k |
| update | ~29 | below |
| pushed fill | ~39 | below |
| overflow | ~52 | below |
| **new this session** | **130** (incl. header/wrappers) | |

Running C6 forcing total: 231 + 130 = **361 lines**. Caveat: the earlier projection for update + overflow + pushed fill was 50-90; actual 130,
because each family got three layers (force / hold / run form). Per-family cost is under the reference, but the sub-total is over its projection.
Remaining C6 (projected, unchanged): `depth_cover` assembly 40-80, induction 50-100, accept 50 -> C6 excl. init **~0.50k-0.60k** (was 0.42k-0.55k).
Whole-project estimate left at 10.4k-14.4k; the ~0.05k C6 overshoot is inside the C reserve, not claimed as saved.

## H constraints checked against P2's H (`H = m + c*T + d + 1`, c = `pushBound M`, d = `depth M`) - **BOTH FAIL as literally stated**

P2's H exists only as prose (no Lean definition of H yet), so this is checked on the formula. Lean witnesses in `ScratchH.lean` (scratch, imports Sit + Comp,
compiles with no output): `exM_pushBound : pushBound exM = 4` (`rfl`), `depth exM = 6` (`ex_depth`).
1. `l + (T+1)*d <= H` (taking `l = m`, the largest admissible input bound) reduces to `(d - c)*T <= 1`. `pushBound` sums pushes over labels while `depth` counts
   pops/peeks/pushes on a path, so `d > c` is possible. Witness `exM_H_fails_c1`: for exM (c = 4, d = 6) and `T = 2`, `m + 18 <= m + 15` is false for every `m`. **P2's H fails constraint 1.**
   Cause: the constraint came from `stepI_height` (growth `depth M` per step), not from a real need. With the growth bound `pushBound` the real requirement
   `m + c*T <= H - d` does hold for P2's H. Two fixes, either is small: (A) redefine `H := m + (T+1)*d + 1` (still polynomial; H is a free parameter in every lemma built so far, so
   nothing built changes); (B) prove a `pushBound`-based height lemma and keep P2's H. **Recommendation: (A). Needs your decision; I have not edited P2.**
2. `H >= 2d`: `H = m + cT + d + 1 >= 2d` iff `m + cT + 1 >= d`, false for small `m, T` (witness `exM_H_fails_c2`, `m = 1, T = 0`; c = 0 machines are worse). **But the constraint is
   not needed.** It came from covering the window `j < d` with pushed-fill and in-range depths only. Now that overflow forcing exists, `depth_cover` (proved) says every `j < H` is a pushed-fill,
   in-range or overflow target when `pl, cn <= H`, so `depth M <= H` suffices. This is a paper argument until the assembly lemma is written (not started).
   Retract "H >= 2d" from the constraint list; the remaining list is `depth M <= H` and constraint 1 (fix A or B).

Lakefile: no change. Not started: `depth_cover` assembly, induction, accept, init, C5.


# H CORRECTION + DEPTH_COVER ASSEMBLY (2026-09-30, sixth session)

## Decision applied
User chose fix (A). P2 now reads `H = m + (T+1)·d + 1`, `d = depth M` (the old `m + c·T + d + 1`, `c = pushBound M`, is recorded
there as a correction). This corrects prose already written. It adds no content, so on its own it does not move the line estimate.

## Targets (written BEFORE any proof)

**H1. Constraint 1, re-verified formally.** In Sit.lean (not only scratch), since the induction will need it:
* `capH m T d := m + (T+1)*d + 1`.
* `runI_height`: `((runI M c t).stk k).length ≤ (c.stk k).length + t * depth M` (iterate `stepI_height`).
* `capH_height`: `s.length ≤ m`, `t ≤ T` ⇒ `∀ k, ((runI M (initList M s) t).stk k).length ≤ capH m T (depth M) - depth M`.
  This is the `hh` hypothesis of every C6 run lemma, discharged. It is stronger than the prose constraint `ℓ + (T+1)d ≤ H`.
* `depth_le_capH`: `depth M ≤ capH m T (depth M)` (the `hdH` hypothesis).
* Scratch witness (ScratchH.lean): constraint 1 now holds for exM for all `m, T` (the case that failed before).

**H2. Constraint 2 (`H ≥ 2d`), decided explicitly.** Expected: holds outright for `T ≥ 1`; fails for `T = 0` when `d > m + 1`
(Lean witness with exM, `m = 1`). Whether it is *needed* is answered by D below: if `cells_step_run` is proved with only `hh` and
`depth M ≤ H`, the constraint is not needed, and that is then proved, not argued on paper.

**D. depth_cover assembly.** For `c := runI M (initList M s) t`, `i := sitIdx c`, `p := pl i k`, `q := cn i k`:
1. `region_cover` (arithmetic): for all `p q H j` with `j < H`, exactly one of
   `j < p` (pushed fill), `p ≤ j ∧ j < H - max p q + p` (in-range shift), `H - max p q + p ≤ j ∧ j < H` (overflow).
   These are literally the depth hypotheses of `pf_step_run`, `sh_step_run_pos`, `ov_step_run`.
2. `cells_step_run`: S-def family and shift family satisfied by `a`, `t < T`, `hh`, `depth M ≤ H`, `CodeHolds a H t c`,
   `CellsHold a H t (cell c)` ⇒ `CellsHold a H (t+1) (cell (runI (t+1)))` (every `k < KK`, every `j < H`).
3. `row_step_run`: adds the update family, concludes `CodeHolds` ∧ `CellsHold` at row `t+1`. This is the one-step invariant.
   The induction over `t` is NOT part of this session.
4. `row_step_capH`: the same with `H := capH m T (depth M)`, hypotheses `hh`/`hdH` replaced by `s.length ≤ m`.

Success = all of the above with no hypothesis beyond those listed (in particular, no `2d ≤ H`), 0 or 1 fix rounds, ~40–80 lines.
Would count as "more than expected": needing any relation between regions and `H` beyond `pl, cn ≤ depth M ≤ H`, or needing one-hot.

## Results (same session, checked against the targets above)

Inserted at the end of Sit.lean section `[C6]`: Sit 1609 -> 1714 lines (+105, CRLF kept). The scratch compile (a file importing
the built `Sit`) passed on the first try: 0 fix rounds. `lake build`: `Build completed successfully (1264 jobs)`, `Built Sit (203s)`. The
only warnings are the three existing `sorry`s (Challenge.lean:3, CookLevin.lean:803, SatInP.lean:15). Banned-token scan of Sit.lean and
ScratchH.lean: no hits. `#print axioms` (run from ScratchH.lean):
`capH_height`, `runI_height`, `region_cover`, `Enc.cells_step_run`, `Enc.row_step_run`, `Enc.row_step_capH` -> `[propext, Classical.choice, Quot.sound]`;
`depth_le_capH`, `capH_c1`, `capH_c2`, `initList_height` -> `[propext, Quot.sound]`. Scratch witnesses `exM_capH_c1`, `exM_capH_c2_fails_T0`,
`exM_capH_c2`, `exM_H_fails_c1` -> `[propext, Classical.choice, Quot.sound]`. No `sorryAx` anywhere.

**H1. Constraint 1 holds, checked formally in two forms.** (a) The prose form `ℓ + (T+1)·d ≤ capH m T d` for `ℓ ≤ m` is `capH_c1`, and its
exM instance, `exM_capH_c1` in ScratchH, is the exact case that `exM_H_fails_c1` refuted for the old `H`. (b) The form the proofs actually
consume is stronger: `capH_height` shows that every row `t ≤ T` of `runI (initList s)` has all heights `≤ capH − depth M` when `|s| ≤ m`.
That is the `hh` hypothesis of every C6 run lemma, now discharged. `depth_le_capH` discharges `hdH`. `row_step_capH` is the one-step invariant
with both discharged: the only assumption left is `|s| ≤ m`, and the init family must force that bound (NOTES "Item 5", point 3).

**H2. Constraint 2 (`2d ≤ H`): not needed. It holds outright only for `T ≥ 1`.** Proved: `capH_c2` (`1 ≤ T ⇒ 2d ≤ capH m T d`). Refuted
at `T = 0`: `exM_capH_c2_fails_T0` (`m = 1`: `12 ≤ 8` is false). The constraint is **unnecessary, and this is now proved, not argued on
paper.** `cells_step_run`/`row_step_run` assume only `hh` and `depth M ≤ H`, nothing like `2d ≤ H`. The constraint list for `H` is final:
`depth M ≤ H` plus the height precondition, and `capH` meets both.

**Step 4: nothing proved depended on P2's old H.** Checked mechanically, not assumed. (i) `pushBound` or `Comp.` occurs in no file of
Prog/D3Fam/D3OneHot/D3Shift/D3SDef/Sit, and none of them imports Comp (only ScratchH does). (ii) A balanced-bracket scan of every binder in every
`theorem/def/structure` signature of those six files (script `hscan2.py`, scratchpad) found that every hypothesis mentioning `H` is a generic bound
(`L.d ≤ H`, `depth M ≤ H`, `p ≤ H`, `c ≤ H`, `j < H`, `u + max … < H`, heights `≤ H` or `≤ H − depth M`) or uses `H` as a parameter
(`numVars T H`, `rowW H`, `cnfSat (… T H …)`, counter fields). (iii) The only places `H` is instantiated with an expression are `H' := T + H + 1` in
the three time-bound monotonicity steps (`gen_time`/`oh_time`/`sh_time` collapse), which has nothing to do with the cap. So `H` is a free
parameter everywhere. **Prose did depend on it:** three NOTES passages said the old `H` "provides" the height precondition (P3 spike note,
CELL-SHIFT overflow note, B1 session). Each now has a dated correction. The plan row **A5** (`height_le ≤ m + c·t`, "reuse Comp `pushBound`")
had the same mistake. It is superseded by `runI_height` + `capH_height`, and A5 is now **proved**.

**D. depth_cover assembly: as expected, no surprise.** `region_cover` is one `omega`, with no hypotheses at all: the three regions are stated as
the literal depth hypotheses of `pf_step_run` / `sh_step_run_pos` / `ov_step_run`, so "exactly one" is interval arithmetic. The overflow
region may be empty (`cn ≤ pl`), and that is harmless. `cells_step_run` is the S-def lemma (`sd_step_run`, for `hS`) plus a 3-way `rcases`
into the three run lemmas. `row_step_run` adds `upd_step_run`. No one-hot, no new invariant, no relation between the regions and `H`
beyond what the run lemmas already take. The existing `D3SH.depth_cover` (∃-form) was not needed; the new one is in the form the run lemmas consume.

What the assembly does not do: the induction over `t` (base = init family, not started). The one-step lemma is stated for `t < T`. The
induction will need `hh` at every `t < T`, and `capH_height` gives it for all `t ≤ T`.

## Line counts

| part | lines |
|---|---|
| `capH`, `runI_height`, `initList_height`, `capH_height`, `depth_le_capH`, `capH_c1`, `capH_c2` (A5 + constraints) | ~48 |
| `region_cover` | 11 |
| `cells_step_run` | 20 |
| `row_step_run`, `row_step_capH` | 27 |
| **total** (incl. header/namespace) | **105** |

The depth_cover assembly proper (region + cells + row, ~58) is inside its projection of 40–80. The other ~48 lines are A-block content
(A5 and the cap), which was not in the C6 projection.

## Updated P6 estimate (supersedes the fifth session's)

| Block | Estimate | Basis |
|---|---|---|
| **D total** | ≈ 6.55k–8.25k | unchanged |
| A (plumbing) | **250–450** (was 300–500) | A5 done (~0.05k, measured); rest unmeasured |
| **B** | ≈ 0.74k, DONE | measured |
| C (tableau semantics) | 2.8k–4.7k unchanged; C6 now **0.42k done** (forcing 0.36k + assembly 0.06k; the cap's 0.05k is counted under A) | |
| C6 sub-band (excluding init) | **~0.52k–0.57k** (was 0.50k–0.60k) | 0.42k done + induction 50–100 + accept ~50 |
| **Total** | **≈ 10.4k–14.4k lines** | unchanged |

The H fix itself corrects prose and adds nothing: it moves no estimate. What applying it turned up is the A5 row. A5 is now done by a
different route (depth growth, not `pushBound`), and it cost ~0.05k lines. This is inside the A band, so the total does not change.
Nothing else needed adjustment. Lakefile: no change. Not started (as instructed): the row-`t` induction, accept, init, C5.

# ROW-t INDUCTION (2026-09-30, seventh session): statement and decision written BEFORE any proof

## The statement (all objects already exist in Sit.lean `[C6]`)

Fix `M : FinTM2`, `E : Enc M`, an assignment `a : List Bool`, `T`, `H`, and a certificate/input `s : List (M.Γ M.k₀)`.
Write `c t := runI M (initList M s) t` (the real, idle-extended run) and `Inv t := E.CodeHolds a H t (c t) ∧ E.CellsHold a H t (E.cell (c t))`.

**I1 (`Enc.rows_run`).** Hypotheses:
* `hu`: `cnfSat (D3Fam.family E.layout E.la E.na E.wa T H E.N) a` (update clauses; the family already ranges over every `t < T`),
* `hs`: `cnfSat (D3Fam.family E.layout E.la E.sa E.wa T H E.N) a` (S-def clauses, every `t < T`),
* `ha`: `cnfSat (D3SH.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a` (shift / overflow / pushed-fill clauses, every `t < T`),
* `hh`: `∀ t < T, ∀ k, ((c t).stk k).length ≤ H − depth M`, and `hdH : depth M ≤ H`,
* `h0 : E.Row0 a H s` (the row-0 obligation, see below).

Conclusion: `∀ t ≤ T, Inv t`.

**I2 (`Enc.rows_capH`).** Same at `H := capH m T (depth M)`, with `hh`/`hdH` replaced by `s.length ≤ m` (via `capH_height`, `depth_le_capH`).

**I3 (`Enc.rows_of_init`).** The form the init family will plug into: from
`InitObl a m T := ∃ s, s.length ≤ m ∧ E.Row0 a (capH m T (depth M)) s` and `hu hs ha` at `H = capH`, conclude
`∃ s, s.length ≤ m ∧ ∀ t ≤ T, Inv t` (for that `s`).

**What "matches" means (explicit, to avoid overclaiming).** The invariant is POSITIVE ONLY: every literal that the real
configuration `c t` would set true (its (label,state) code literal, and for each `k < KK`, `j < H` the literal of cell value
`E.cell (c t) k j`) is true in `a`. It does NOT say the other literals are false (no one-hot / exactness). Exactness, where
needed (row 0 to construct `s`; row T for accept, if needed there), is a separate matter.

## What the base case needs from the (not yet built) init family

`E.Row0 a H s := E.CodeHolds a H 0 (initList M s) ∧ E.CellsHold a H 0 (E.cell (initList M s))`, i.e.
(i) the code literal of `initList M s` (label `M.main`, state `M.initialState`) is true at row 0;
(ii) for every stack `k < KK` and depth `j < H`, the literal of `E.cell (initList M s) k j` is true at row 0 (the input/certificate
stack `k₀` holds `s`, all other stacks empty, i.e. their bottom cells);
plus (iii) `s.length ≤ m`, the bound `capH_height` needs. Since `s` is chosen by the assignment, (iii) is not a property of
the run: the init family must force it (bottom value at row 0, stack `k₀`, depths `j ≥ m`) and the lemma must produce it.

## Decision (item 2): PLACEHOLDER as an explicit hypothesis, not a stub declaration

I will complete the induction now, with the row-0 obligation as a **named definition `Enc.Row0` taken as a hypothesis**
(and `Enc.InitObl` for the existential form). Reasons:
* The induction's only dependency on init is through that one proposition. Stating it as a hypothesis keeps the gap
  visible in every signature, with no `sorry`, no `axiom`, nothing that `#print axioms` would hide.
* Holding off would leave the step lemma untested as a chain (e.g. an off-by-one between `t < T` for the families and
  `t ≤ T` for `hh`) until init exists; doing it now tests that.
* The risk of a placeholder is that it is mistaken for done. Mitigation: the docstrings of `Row0`/`InitObl` say PLACEHOLDER,
  the lemma table row says "conditional on `InitObl`", and a "what init must prove" subsection is written below after the proof.
What this is NOT: a proof that any satisfying assignment corresponds to a run. That needs `InitObl` from the init family
clauses (unbuilt), and the whole theorem is only as strong as `Row0` is faithful.

Expected cost: 50–100 lines (P6 projection). Expected machinery: none beyond `row_step_run` + `capH_height` (induction on `t`).

## Results (same session, checked against the statement above)

Proved in Sit.lean, end of section `[C6]` (new sub-block "Row-`t` induction", Sit 1714 -> 1776 lines, +62, CRLF kept):
`Enc.Row0` (def, PLACEHOLDER), `Enc.InitObl` (def, PLACEHOLDER), `Enc.rows_run` (I1), `Enc.rows_capH` (I2), `Enc.rows_of_init` (I3),
exactly as stated above, no extra hypotheses.

**Machinery: nothing beyond chaining the existing one-step lemma.** `rows_run` is `induction t`: base = `h0`, step =
`row_step_run` at `t < T` with `hh t`. `rows_capH` discharges `hh` with `capH_height` (it holds for all `t ≤ T`, so `t < T` is
more than enough) and `hdH` with `depth_le_capH`. `rows_of_init` unpacks the `∃`. No new lemma, no one-hot, no off-by-one:
the families' `t < T` range and `hh` on `t < T` line up with the conclusion on `t ≤ T`.

Fix rounds: 1, not mathematical. The first scratch compile auto-bound `cnfSat` as an implicit variable, because scratch
`lake env lean` ignores the lakefile's `autoImplicit=false` (known pitfall) and the scratch file lacked `open PvsNP.SATDef`.
That made the hypotheses `sorry`-typed, and `#print axioms` showed `sorryAx`. Fix: `open PvsNP.SATDef` plus
`set_option autoImplicit false` in the scratch. After that it was clean on the first try.

Checks (run this session, output quoted):
* `lake build`: `Build completed successfully (1264 jobs).` The only warnings are the three existing `sorry`s
  (Challenge.lean:3:8, CookLevin.lean:803:8, SatInP.lean:15:8).
* `#print axioms` (ScratchRow.lean, `import Sit`):
  `rows_run`, `rows_capH`, `rows_of_init` -> `[propext, Classical.choice, Quot.sound]`; `Row0`, `InitObl` -> `[propext, Quot.sound]`.
* Banned-token scan of Sit.lean and ScratchRow.lean: no hits.

**Not tested: non-vacuity of the hypothesis set.** Nothing this session shows that some `a` satisfies the three families and
`InitObl` together. That is the completeness direction of the reduction (C5), not started. So `rows_of_init` is a correct
conditional, but it has not been shown to be non-vacuous.

## What the real init family must prove to discharge the placeholder (DO NOT treat `InitObl` as done)

Target lemma, to be stated when init is built (shape fixed now):
`init_obl : cnfSat (initFamily …) a → (one-hot at row 0, if kept separate) → E.InitObl a m T`, i.e. build from `a` a list
`s : List (M.Γ M.k₀)` with
1. **`s.length ≤ m`**: forced by init clauses putting value `0` (empty) at row 0, stack `k₀`, every depth `m ≤ j < H`.
   Convention checked (Sit.lean:677): `Enc.cell c k j = ((c.stk (kd k))[j]?).elim 0 enc`, so `j` is the list index from
   the head (the top) and `0` means past the end. With prefix form, `0` at `j = m` already gives `|s| ≤ m`.
   `capH_height` consumes exactly this bound.
2. **`CodeHolds a H 0 (initList M s)`**: the code literal of (`M.main`, `M.initialState`) is set true at row 0 by a unit clause.
   This part does not depend on `s`.
3. **`CellsHold a H 0 (E.cell (initList M s))`** for all `k < KK`, `j < H`:
   * `k ≠ k₀`: the empty-stack cell value at every depth, by unit clauses;
   * `k = k₀`: the cells of `s`. `s` must be *read off* `a`. The route recorded in C1: row-0 one-hot (at least one, at most one)
     ⇒ an array `w` with `Tr a (cIdx H 0 k₀ j (w k₀ j))`; init clauses ⇒ `RowOK H w` (valid codes `≤ sz`, prefix form: no
     non-bottom below a bottom); set `s := (decRow H n w).stk k₀`, then `enc_decRow` gives `cell (initList M s) = w`.
   * If the input part of `k₀` is fixed by the instance `x` (Cook–Levin: input + certificate), the clauses must also force
     those cells, and the lemma must state `s = x ++ y` (or whatever `initList` order is), with `|y|` bounded. `InitObl`
     as stated does not mention the input yet. **It must be strengthened to pin the input part before accept/C5 use it.**
     Otherwise the reduction would accept any start stack, and that would be a wrong reduction, not just a gap.
4. Everything at `H = capH m T (depth M)` with the same `m` as in (1).

Once `init_obl` exists, `rows_of_init` gives the full-run invariant without further work. The strengthening in 3 (input pinned)
will change `InitObl`'s statement, but not `rows_run`/`rows_capH`: those are stated for arbitrary `s`.

## Line count

| part | lines |
|---|---|
| header + `Row0` + `InitObl` (defs, docstrings) | 15 |
| `rows_run` | 20 |
| `rows_capH` | 11 |
| `rows_of_init` | 13 |
| namespace/variable lines | 3 |
| **total** | **62** |

Projection was 50–100, so this is at the low end, as expected for a pure chain. Running C6: 0.42k + 0.06k = **0.48k done**.
C6 excluding init: 0.48k + accept ~50 → **~0.52k–0.55k** (was 0.52k–0.57k; the top shrinks because the induction is measured).

## Updated P6 estimate (supersedes the sixth session's)

| Block | Estimate | Basis |
|---|---|---|
| **D total** | ≈ 6.55k–8.25k | unchanged |
| A (plumbing) | 250–450 | unchanged |
| **B** | ≈ 0.74k, DONE | measured |
| C (tableau semantics) | 2.8k–4.7k unchanged; C6 **0.48k done** | forcing 0.36k + assembly 0.06k + induction 0.06k |
| C6 sub-band (excluding init) | **~0.52k–0.55k** | 0.48k done + accept ~50 |
| **Total** | **≈ 10.4k–14.4k lines** | unchanged (the saving is < 0.05k) |

Lakefile: no change. Not started, as instructed: the real init family, accept, C5. Status: **NOT PROVED**. `sat_in_p` (the open
problem) is untouched, and Cook–Levin hardness is still `sorry`.

---

# INIT FAMILY + STRENGTHENED `InitObl` (2026-10-01): statement written BEFORE any proof

## Lakefile

No change planned. Everything goes at the end of Sit.lean's `[C6]` section (Sit is already a root, so `lake build` checks it).

## Where `x` and `y` come from (the instance, not a free stack)

For the verifier `M` of an NP language (A2), the start stack is `map inv (encode (w, y'))` with the repo's
`pair_encoding`: `map inl (ea w) ++ inr none :: map (inr ∘ some) y'`. Top of stack = head of the list
(`initList` puts `s` on `k₀`, and `Enc.cell` reads index `j` from the head). So at the Sit level (generic `M`):
* `x : List (M.Γ M.k₀)`: the **fixed** prefix (instance symbols and the separator `#`). It is a parameter of the
  family, that is, it is the reduction's input. The assignment cannot change it.
* `Ys : List (M.Γ M.k₀)`: the **allowed certificate symbols** (later: `inv ∘ inr ∘ some` over `Γ₁`). This is also part
  of soundness. If the certificate cells could hold any `Γ k₀` symbol (a second `#`, or an `inl` symbol), the tracked
  run would be on a string that is not `encode (w, y')` for any `y'`, and the verifier's spec says nothing about such strings.
* `y`: chosen **from the assignment**, `y ∈ Ys*`, with `|x ++ y| ≤ m`.

## The strengthened statement (replaces the placeholder `InitObl`)

```lean
def InitObl (a : List Bool) (x Ys : List (M.Γ M.k₀)) (m T : ℕ) : Prop :=
  ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
    E.Row0 a (capH m T (depth M)) (x ++ y)
```
`Row0` itself is unchanged (`CodeHolds ∧ CellsHold` of `initList M s` at row 0). Against last session's four conditions:
1. length bound: `(x ++ y).length ≤ m` (was `s.length ≤ m`);
2. code literal: `CodeHolds` inside `Row0` (unchanged);
3. other stacks empty: `CellsHold` at `k ≠ kc k₀` inside `Row0`, cell value `0` (unchanged);
4. `k₀` cells: `CellsHold` at `kc k₀` for the cells of **`x ++ y`** (was: of an arbitrary `s`). **New:** `s` is
   no longer existential. Only `y` is, and only over `Ys`.

**Predicted route change (to be checked by the proof): `decRow`/`enc_decRow` should not be needed.** The invariant is positive
only (`CellsHold`, not `CellsAre`). So `y` can be built directly by choice from the at-least-one clauses: at each
certificate depth, some allowed symbol's literal is true, or the ⊥ literal is. No row-0 one-hot and no `RowOK` are needed. If
the proof needs exactness after all, I will record that here.

## The init clause family (`Enc.initFamily x Ys m T H`), all dense over `layout.numVars T H`, all at row 0

Write `k₀' := kc k₀`, `Z j := cIdx H 0 k₀' j 0` (⊥ at depth `j` of the input stack).
* (I1) code unit: `X[0, lc (some main, initialState)]`;
* (I2) other stacks empty: `C[0,k,j,0]` for `k < KK`, `k ≠ k₀'`, `j < H`;
* (I3) input pinned: `C[0,k₀',j, enc x[j]]` for `j < |x|`;
* (I4) certificate cell, at least one: `Z j ∨ ⋁_{z ∈ Ys} C[0,k₀',j, enc z]` for `|x| ≤ j < m`;
* (I5) prefix form: `¬Z j ∨ Z (j+1)` for `|x| ≤ j < m`;
* (I6) length bound: `Z j` for `m ≤ j < H`.

## The target lemmas

* **`init_row0`** (general `H`): `x.length ≤ m`, `m < H`, `cnfSat (E.initFamily x Ys m T H) a` ⇒
  `∃ y, (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧ E.Row0 a H (x ++ y)`.
* **`init_obl`**: the same at `H = capH m T (depth M)` (`m < capH` always holds), concluding `E.InitObl a x Ys m T`.
* **`rows_of_init`** restated with the new `InitObl`: conclusion `∃ y ∈ Ys*, |x ++ y| ≤ m ∧ ∀ t ≤ T, invariant of
  runI M (initList M (x ++ y)) t`.

**Prediction to verify, not assume: `rows_run` and `rows_capH` need no change.** They take an arbitrary `s`, and the new
`rows_of_init` should just apply `rows_capH` at `s := x ++ y`. The check: those two declarations stay byte-identical in
Sit.lean, and the build passes.

**Not claimed (and not needed for this lemma):** that the assignment encodes *only* `x` at row 0, meaning that other literals are
false. The positive invariant does not give that. Soundness of the whole reduction therefore still needs at-most-one where acceptance is read
(row `T` code block and output cells), which is the accept session's job. With positive literals only, the all-true assignment
satisfies every family `rows_run` uses, and init too (each of their clauses has a positive literal). So **some at-most-one family is required for soundness**.
This is a known obligation of accept, not a gap in init.

Generator (D-block): **not in this session's scope as a proof.** The design assessment is in the results below.

## Results (same session, checked against the statement above)

Proved in Sit.lean, end of section `[C6]`. There is a new sub-block "The init family (row 0) and its semantics". Sit.lean went from 1776 to 1943 lines (+167), CRLF kept.
Declarations: `cnfSat_append`, `unit_force`, `Enc.zIdx`, `Enc.initCode`/`initOther`/`initIn`/`initCert`/`initPre`/`initTail`
(I1 to I6), `Enc.initFamily`, `Enc.initList_k₀`, `Enc.initList_ne`, **`Enc.init_row0`**, **`Enc.init_obl`**, **`Enc.rows_of_initFamily`**.
Changed: `Enc.InitObl` (strengthened, exactly as stated above) and `Enc.rows_of_init` (now concludes about `initList M (x ++ y)`).
No extra hypotheses beyond those stated. `init_row0` takes `x.length ≤ m`, `m < H` and `cnfSat (initFamily …)`. `init_obl` takes only `x.length ≤ m`, because `m < capH` is
discharged by `unfold capH; omega`.

**`rows_run`/`rows_capH` unchanged: verified, not assumed.** I hashed the text from `theorem` to the end of the proof before and after the edit:
`rows_run 8725c1e218af → 8725c1e218af`, `rows_capH b4b1aac7a7a2 → b4b1aac7a7a2`. Only their docstrings changed, to drop the word
"PLACEHOLDER". The new `rows_of_init` is the old proof with `s := x ++ y`, and `lake build` accepts it.

**Route: the prediction held. No `decRow`, no `enc_decRow`, no `RowOK`, no row-0 one-hot.** `y` is built directly. Let `ℓ := Nat.find` of
"`|x| ≤ j` and `Z j` is true". It exists because I6 makes `Z m` true, and `ℓ ≤ m`. For `|x| ≤ j < ℓ`, `Z j` is false, so I4 gives some `z ∈ Ys` whose literal is
true. `y := List.ofFn` of `Classical.choose` of those. For `j ≥ ℓ`, `Z j` holds by `Nat.le_induction` with I5 (below `m`) and I6 (from `m` on).
`Enc.cell (initList (x++y))` on `k₀` is read through `cell_kc` and `getElem?_append_left/right` plus `getElem?_ofFn`. Other stacks
give `0` (I2). The code is I1. Decoding is unnecessary because the invariant is positive. Any true allowed literal is a valid choice.

Fix rounds: 3, none mathematical. (1) The scratch was missing `open Turing` (`FinTM2`/`initList` unknown). (2) Anonymous-constructor
membership proofs had no expected type; fixed by writing `j = |x| + i` first (`Nat.exists_eq_add_of_le`) and typing `hm`. (3) A
`rw` hit a dependent motive through `Classical.choose`; fixed by the same `j = |x| + i` substitution. After that the build was clean.

### Item 2: does init need its own generator? **Yes, a new machine. It is partly a reuse of patterns, and it has one genuinely new primitive.**

The clause list is now a Lean definition (`initFamily`, 37 lines). It is not yet emitted by any `FinTM2`. The D-block generator is **not built**.
Assessment of what it needs:
* I2 (`k ≠ k₀'`, `j < H` units), I6 (`m ≤ j < H` units), I5 (2-literal clauses over `j`): runtime loops over `k`/`j` emitting fixed-shape
  dense clauses. **Same pattern as D3OneHot** (runtime `k, j` loops, unit/2-literal dense clauses).
* I4: one clause per `j`, with `|Ys| + 1` literals at codes `0` and `enc z`. **Same pattern as D3Shift's label chains** over a finite table
  (codes are hard-wired constants of `M`).
* I1: one constant unit clause. Trivial.
* **I3 is new: the clause depends on the input content**, since the literal position contains `enc x[j]`. No existing family reads the input
  symbols. They use the input only through counters. This needs the "input symbol into the label" primitive already named in P4/D2
  (read the top input symbol, branch to a label per symbol, emit that symbol's unit clause). That primitive and the `x` construction
  (`map inl (ea w) ++ [#]`) are the real new D work.
Estimate for the generator: unchanged at the P6 line "init + input decoding 600–1000". Nothing measured this session moves it.

### Item 4: line count (no prior budget) and character

| part | lines |
|---|---|
| sub-block header | 2 |
| library: `cnfSat_append`, `unit_force` (+ namespace/variable lines) | 18 |
| family definitions `zIdx`, I1–I6, `initFamily` | 37 |
| `initList_k₀`, `initList_ne` | 6 |
| `init_row0` | 82 |
| `init_obl` | 5 |
| `rows_of_initFamily` | 15 |
| **new block** | **165** |
| `InitObl` / `Row0` / `rows_of_init` edits (net) | +2 |
| **Sit.lean total change** | **+167** |

**Character:** this is a C6 forcing lemma in kind (read clauses, conclude literals), plus a choice construction. The semantic part
(`init_row0` + helpers ≈ 105) is somewhat above the 0.09k–0.14k per-family C6 forcing cost. The excess is the `Nat.find`/`List.ofFn`
construction of `y`, which the transition families did not need. The **family definition** costs 37 lines. The D3 files were not expensive
because of their definitions (each was tens of lines) but because of the generator machine and its time bound (600–1000 each), and that part is
exactly what is unbuilt here. So: C6-like cost measured (~0.17k), D-like cost still ahead (600–1000).

### Item 5: does `InitObl` now genuinely pin the input? **Yes.**

Reasoning: `InitObl a x Ys m T` existentially quantifies only `y`. The start stack in `Row0` is the term `x ++ y`, with `x` a parameter
of the family, i.e. the reduction's input. So `rows_of_initFamily`'s conclusion speaks about `runI M (initList M (x ++ y))`. The run
the assignment tracks starts with the actual instance prefix. Its certificate part is restricted to `Ys` symbols, which closes
the second half of the gap (no foreign `Γ k₀` symbols in the certificate region). The old form `∃ s, |s| ≤ m ∧ Row0 … s` let the tracked run
start anywhere. The new form does not. Last session's soundness gap ("the reduction would accept any start stack") is closed at
this interface.

What "pinned" does **not** mean (stated so it is not overclaimed): the assignment may still set *extra* row-0 literals true, for example
both `C[0,k₀',j,enc x[j]]` and some other code. Pinning is about which run is tracked, not about the exactness of row 0. As recorded
before the proof, positive-only invariants are satisfied by the all-true assignment, so **soundness of the full reduction still needs
an at-most-one family where acceptance is read** (row `T` code block and output cells). That belongs to accept, not to this gap.

### Non-vacuity (not proved; C5)

Not proved this session: that the init family is satisfiable together with the transition families. Paper check of the obvious danger,
to be proved in C5: `denseClause V ls` silently **drops** literals at positions `≥ V`, and an all-dropped clause is unsatisfiable. Every init
literal sits in row 0 at `xIdx H 0 c` (`c < A0 ≤ A`) or `cIdx H 0 k j v` (`k < KK`, `j < H`, `v < g`, using `enc z ≤ sz k₀ < g` via
`input_mem`/`enc_dec`; I5 uses `j + 1 ≤ m < H`), so all are `< rowW H ≤ numVars T H`. The exact one-hot image of `initList (x ++ y)`
with `|x ++ y| ≤ m`, `y ∈ Ys*` satisfies I1–I6: I5 by prefix form, I4 since each certificate cell is `⊥` or `enc` of some `z ∈ Ys`.
That is C5's init case. It is not attempted here.

### Checks (run this session, output quoted)

* `lake build`: `✔ [1263/1264] Built Sit (94s)` / `Build completed successfully (1264 jobs).` The only warnings are the three existing `sorry`s
  (Challenge.lean:3:8, CookLevin.lean:803:8, SatInP.lean:15:8).
* `#print axioms` (ScratchInit.lean, `import Sit`):
  `init_row0`, `init_obl`, `unit_force`, `rows_run`, `rows_capH`, `rows_of_init`, `rows_of_initFamily` → `[propext, Classical.choice, Quot.sound]`;
  `cnfSat_append`, `zIdx`, `initCode`, `initOther`, `initIn`, `initCert`, `initPre`, `initTail`, `initFamily`, `initList_k₀`, `initList_ne`,
  `InitObl`, `Row0` → `[propext, Quot.sound]`. No `sorryAx`.
* Banned-token scan (sorry, admit, axiom, native_decide, decide +native, implemented_by, @[extern, unsafe, partial, open private,
  set_option debug, run_cmd, addDecl) of Sit.lean and ScratchInit.lean: `no hits`.

### Updated P6 estimate (supersedes the seventh session's)

| Block | Estimate | Basis |
|---|---|---|
| **D total** | ≈ 6.55k–8.25k | unchanged; includes init generator + input decoding 600–1000 (**unbuilt**) |
| A (plumbing) | 250–450 | unchanged; must supply `x = map inv (map inl (ea w) ++ [inr none])`, `Ys = image of inv ∘ inr ∘ some`, `m = |x| + |w|^k` |
| **B** | ≈ 0.74k, DONE | measured |
| C (tableau semantics) | 2.8k–4.7k unchanged; C6 **0.65k done** (0.48k + init semantics 0.17k) | init semantics was inside the unmeasured C band |
| C6 remaining | accept ~50–150 (now known to need at-most-one at row `T`, so the label/state one-hot family's semantics too) | |
| **Total** | **≈ 10.4k–14.4k lines** | unchanged |

**Status of `rows_run`/`rows_capH`/`rows_of_init` now:** the chain `rows_of_initFamily` is conditional only on **clause hypotheses**
(`cnfSat` of the update, S-def, shift and init families, plus `|x| ≤ m`). There is no placeholder proposition left in it. What remains before the
Cook–Levin argument is unconditional: (i) **C5**: the real run's assignment satisfies all these families (non-vacuity; also the
dropped-literal check above); (ii) **accept** plus the at-most-one semantics needed to read acceptance (soundness to `R w y'`); (iii) the
generators for init/one-hot/accept (D) and the plumbing (A).

Lakefile: no change. Not started, as instructed: accept, C5. Status: **NOT PROVED**. `sat_in_p` (the open problem) is untouched, and Cook–Levin
hardness is still `sorry`.

---

# ACCEPT FAMILY + LITERAL-RANGE CHECK (2026-10-01, second): statement written BEFORE any proof

## Lakefile

No change planned. Semantics go at the end of Sit.lean `[C6]` (a root). If a generator is built it goes in a new
file; adding that file to the roots would need your approval.

## Item 1. What accept must force, and where at-most-one is actually needed

**Acceptance in the repo's model.** A verifier `V` for an NP language has `TM2OutputsInTime V (map inv (encode (w,y')))
(some (map inv [f (w,y')])) p(n)`. This means the real run reaches `haltList V [inv b]` within `p(n)` steps: label `none`, state
`initialState`, `[inv b]` on `k₁`, every other stack empty. `runI` idles once the label is `none`. So at any row `T ≥ p(n)`, the
tracked real configuration is that halted config, and "accepting" means `b = true`, i.e. the top of `k₁` is `acc := inv true`.

**Sit-level definition (generic `M`, `acc : M.Γ M.k₁`):**
`Accepts M c T acc := (runI M c T).l = none ∧ (runI M c T).var = M.initialState ∧ ((runI M c T).stk M.k₁).head? = some acc`.
Since `runI` idles after a halt, `l = none` at row `T` is the same as halting at some row `≤ T`. The repo's `EvalsToInTime` link is plumbing (A).

**The accept family `Enc.accFamily acc T H` (all at row `T`, all dense unit clauses over `numVars T H`):**
* (A1) code block, for every `u < A0`: the unit literal `X[T,u]`, with polarity `u = acode`, where `acode := lc (none, initialState)`.
  So `X[T,acode]` is positive and every other code literal of row `T` is negated.
* (A2) the top cell of `k₁`, for every `x < g`: the unit literal `C[T, kc k₁, 0, x]`, with polarity `x = enc k₁ acc`.

**This *is* "at-least-one + at-most-one" at the two places acceptance is read, in its cheapest form.** Given the positive
unit, "all other literals false" is logically equivalent to "at most one literal true". So the family is `A0 + g` unit clauses, not
`1 + A0(A0−1)/2` pairwise ones. Rows `t < T` get no clause, and neither do other cells of row `T` or the situation block `[A0, A)`.

**How it rules out the all-true assignment.** Each (A1) clause with `u ≠ acode` is a single negative literal. The all-true
assignment falsifies it. Such a `u < A0` always exists: `lc (none, v₀) ≠ lc (some main, v₀)` (since `ld ∘ lc = id`), and both are `< A0`, so `A0 ≥ 2`.
To be proved as `accFamily_allTrue`. The *meaningful* statement is the soundness theorem below. Every satisfying assignment of
init + transition + accept yields an accepting real run. So on a rejecting instance (no `y ∈ Ys*` with `|x++y| ≤ m` accepts) the formula is
**unsatisfiable by every assignment**, the all-true one included (`unsat_of_noAccept`).

**Is at-most-one needed anywhere else (rows `t < T`, the label/state block, other cells)? Checked by argument now, to be
confirmed by the Lean proof using no other at-most-one hypothesis: NO.**
* The invariant `rows_of_initFamily` proves is *positive*: every literal the real run on `x ++ y` would set true is true. The
  real run is determined by `x ++ y` (`runI` is a function). Extra true literals anywhere can only make *more* `S[t,i]` true
  and force *more* literals true. They cannot make a real literal false, so they cannot break the invariant.
* Row 0: `y` is chosen from the true certificate literals. If several are true, *any* choice works. The invariant is then
  proved for that run. Exactness is not needed.
* Row `T`: this is the only place where information flows from the assignment *to* a claim about the run. The claim "the real code is
  `acode` and the real top of `k₁` is `acc`" needs the real literal (true by the invariant) to be the *only* true one in its block.
  That is exactly (A1)/(A2).
* Consequence (a planning finding, if the proof confirms it): the planned **label/state one-hot family is unnecessary**,
  and the built **cell one-hot family (D3OneHot) need not be part of Φ for soundness**. C5 would then have two fewer families to
  satisfy. The one-hot was planned for a decode-then-check soundness proof, which the positive-invariant route never used.

**Target lemmas (Sit.lean, end of `[C6]`):**
* `acc_code`: `cnfSat accFamily a`, `u < A0`, `Tr a (xIdx H T u)` ⇒ `u = acode`.
* `acc_cell`: `cnfSat accFamily a`, `x < g`, `Tr a (cIdx H T (kc k₁) 0 x)` ⇒ `x = enc k₁ acc`.
* **`accept_sound`**: from `|x| ≤ m`, `hacc : ∃ i, dec k₁ i = acc`, and `cnfSat` of update, S-def, shift, init and accept
  (all at `H = capH m T (depth M)`), conclude `∃ y, (∀ z ∈ y, z ∈ Ys) ∧ |x ++ y| ≤ m ∧ Accepts M (initList M (x ++ y)) T acc`.
  `hacc` is an explicit hypothesis. Without it, `enc k₁ acc` is unconstrained (`enc` is only specified on `dec`'s image), and a
  code collision would make the reading wrong. Plumbing (A) must discharge it, for example by putting `acc` into `Enc`'s finite `k₁`
  alphabet. **New A obligation.**
* `unsat_of_noAccept`: the contrapositive, "no accepting certificate ⇒ the conjunction of the five families is unsatisfiable".
* `accFamily_allTrue`: the all-true assignment of length `numVars T H` does not satisfy `accFamily`.
* `trans_allTrue` (a Lean witness for the gap accept closes): the all-true assignment satisfies update, S-def, shift and init.

**Not claimed:** non-vacuity (some assignment satisfies all five families when the verifier accepts). That is C5. So
"no longer trivially satisfiable" is proved in the *soundness* sense: satisfiable ⇒ accepting certificate exists. The *completeness*
sense (accepting certificate ⇒ satisfiable) is not proved, and it is C5's job.

## Item 2. Out-of-range literals: what exactly is at stake, and the lemma

`denseClause V ls = (range V).map (ls.lookup ·)`. A literal `(p, b) ∈ ls` is lost in two ways:
(i) `p ≥ V` (out of range), or (ii) an earlier entry of `ls` at the same `p` with the opposite polarity (`lookup` takes the first one).
**Direction of the risk (correcting the framing in the request):** losing literals makes a clause *stronger* (fewer ways to
satisfy it). An all-lost clause is unsatisfiable, not vacuous. So the C6 forcing lemmas are not undermined. They go through
`clauseSat_dense`, which only ever returns a literal that *is* in `ls` and true in `a`, and that stays valid. What is at stake is
**completeness (C5)**: the real run's assignment must satisfy every clause through a literal that actually survives into the dense clause.
Losing a literal could make Φ unsatisfiable on YES instances, so the reduction would be wrong in the other direction. So
the check is required before C5, but it does not touch any proved forcing lemma.

**Statement.** `Faithful V ls := ∀ p b, (p, b) ∈ ls → p < V ∧ ls.lookup p = some b` (no loss of either kind), and
`FamOK V φ := ∀ c ∈ φ, ∃ ls, c = denseClause V ls ∧ Faithful V ls`. Then:
* `clauseSat_iff`: `Faithful V ls` ⇒ `(clauseSat (denseClause V ls) a ↔ ∃ p b, (p,b) ∈ ls ∧ a[p]? = some b)`. This is the
  exact clause semantics C5 needs.
* `FamOK (numVars T H)` for: update (`depth M ≤ H`), S-def (same), shift/overflow/pushed fill (same), init (`|x| ≤ m < H`), accept (`0 < H`).
  For the D3 families it should come from the existing sortedness (`lits_inc`, `Mono`). For init and accept it comes from a range
  check plus a "no position with both polarities" check.
**If any family fails FamOK under the hypotheses the pipeline actually has, I stop and report it.**

Paper pre-check of one subtle spot: I4's literal list is `Z j :: Ys.map (enc …)`, which is **not sorted** if `Ys` is
unsorted, and it has duplicate positions if two `z ∈ Ys` share an encoding. Both are harmless for `Faithful`, since all polarities are positive.
The *generator* path (`encodeClause_denseClause`), however, needs `Inc`, i.e. sorted. **Init-generator note: emit I4 from
the sorted, deduplicated code list, or prove `denseClause` equality with a sorted list.**

## Results (same session, checked against the statement above)

### Item 2 first: out-of-range / shadowed literals. **Resolved: proved. No family loses a literal under the hypotheses the pipeline has.**

Proved in Sit.lean (new block at the end of `[C6]`):
* `Faithful V ls`, `FamOK V φ`, `FamPos V φ` (FamOK plus "every clause has a positive literal"), exactly as specified above.
* **`clauseSat_iff`**: `Faithful V ls → (clauseSat (denseClause V ls) a ↔ ∃ p b, (p,b) ∈ ls ∧ a[p]? = some b)`. This is the exact clause semantics, and
  C5 can use it directly.
* `faithful_of_inc` (sorted ⇒ faithful), `faithful_of_pol` (in range and no position with both polarities ⇒ faithful), `faithful_pos`, `faithful_single`.
* Per family, at the hypotheses already in the pipeline:
  * **`Enc.upd_pos`** (update) and **`Enc.sdef_pos`** (S-def): `depth M ≤ H`. Via generic `fam_pos` from the existing `D3Fam.lits_inc`.
  * **`Enc.shift_pos`** (shift, overflow and pushed fill, all three clause kinds): `depth M ≤ H`. Via generic `sh_pos` from the existing `shPos_mono`/`ovPos_mono`/`pfPos_mono` + `inc_drop`.
  * **`Enc.init_pos`** (I1–I6): `|x| ≤ m < H`. Proved directly with `faithful_single`/`faithful_pos`, plus `faithful_of_inc` for I5. The symbol codes are `< g` via `input_mem` (`Enc.enc_lt`).
  * **`Enc.acc_ok`** (accept): `0 < H`.
  At `H = capH m T (depth M)` every hypothesis holds: `depth ≤ capH` (`depth_le_capH`) and `m < capH`, `0 < capH` (by `unfold capH; omega`). The plumbing (A) must supply `|x| ≤ m`, which holds by its choice of `m`.
* The I4 subtlety predicted on paper is real but harmless here. Its list is unsorted and may repeat positions, and `init_pos` proves it faithful anyway (all literals are positive).
  **It does matter for the init generator** (`encodeClause_denseClause` needs `Inc`). Recorded as a D note.
* **Answer to the request's worry:** the property holds, so no forcing lemma is undermined. Even if it had failed, the forcing lemmas would have stayed valid. A lost literal makes a clause *stronger*, never vacuous, and `clauseSat_dense` only returns literals that are actually in the list.
  The real dependency was C5 (completeness), and `clauseSat_iff` + `FamOK` now cover it for all five families.

### Item 4: accept forces an accepting halted run, and the all-true assignment no longer works

Proved in Sit.lean, same block:
* Family **`Enc.accFamily acc T H = accCode ++ accCell`** (A1/A2 exactly as specified), `Enc.acode := lc (none, initialState)`.
* **`Enc.acc_code`**: a true code literal at row `T` is `acode`. **`Enc.acc_cell`**: a true top-of-`k₁` literal at row `T` is `enc k₁ acc`. Helper `Enc.unit_pol`.
* `Accepts M c acc := c.l = none ∧ c.var = M.initialState ∧ (c.stk M.k₁).head? = some acc`.
* **`Enc.accept_sound`**: from `|x| ≤ m`, `hacc : ∃ i, dec k₁ i = acc`, and `cnfSat` of the update, S-def, shift, init and accept families (all at `capH`),
  conclude `∃ y, (∀ z ∈ y, z ∈ Ys) ∧ |x ++ y| ≤ m ∧ Accepts M (runI M (initList M (x ++ y)) T) acc`. This is exactly the stated target.
  **No one-hot / at-most-one hypothesis appears besides the accept family.** The proof is `rows_of_initFamily` at `t = T`, then
  `acc_code` on the real code literal (`CodeHolds`) and `acc_cell` on the real top-cell literal (`CellsHold`, `0 < capH`). Then `ld ∘ lc = id` gives label/state.
  `Good` (`run_good`) + `enc_dec` + `hacc` decode the cell to `head? = some acc`.
* **`Enc.unsat_of_noAccept`**: if no `y ∈ Ys*` with `|x ++ y| ≤ m` gives an accepting run at row `T`, then no assignment satisfies the five families together.
* **`Enc.trans_allTrue`** (Lean witness of the gap that accept closes): the all-true assignment of length `numVars T H` satisfies update, S-def, shift and init
  (`depth ≤ H`, `|x| ≤ m < H`). This is the `FamPos` lemmas + `sat_allTrue`.
* **`Enc.accFamily_allTrue`**: the all-true assignment does **not** satisfy `accFamily` (for every `M`, `acc`, `T`, `H`). Uses `Enc.A0_two`
  (`2 ≤ A0`: the codes of `(none, v₀)` and `(some main, v₀)` differ).
* Link to the repo's output notion (A plumbing, reusable for C5): `runI_succ'`, `runI_add`, `runI_halted` (halted configs idle),
  `runI_of_iterate`, **`runI_haltList`**: `TM2OutputsInTime M s (some l') p` and `p ≤ T` ⇒ `runI M (initList M s) T = haltList M l'`.
  **`accepts_haltList`**: `Accepts M (haltList M l') acc ↔ l'.head? = some acc`. So for a verifier with outputs `[inv b]`, `accept_sound`
  plus these two give `b = true` for the certificate found (that last step is A).

**What "no longer trivially satisfiable" means, precisely, and what is shown:**
1. *Shown (soundness sense):* every satisfying assignment of the five families yields a real certificate `y ∈ Ys*`, `|x++y| ≤ m`, whose real run accepts by row `T`
   (`accept_sound`). Contrapositive: on any instance with no accepting certificate, the conjunction is unsatisfiable by **every** assignment (`unsat_of_noAccept`).
   This is a theorem about all degenerate assignments, not only all-true.
2. *Shown (the concrete witness):* all-true satisfies the four earlier families (`trans_allTrue`) and fails accept (`accFamily_allTrue`).
3. *Not shown (completeness sense, C5's job):* that the five families are satisfiable when an accepting certificate exists. Without C5 the
   formula could in principle be unsatisfiable on every instance, which would make it sound but useless. accept sets up the right statement, and C5 must prove its converse.

**Item 1 checked by the proof: at-most-one is needed at row `T` only, and only on the two blocks read.** `accept_sound`'s signature has no other
exactness hypothesis. **Planning consequences:** (a) the planned label/state one-hot family is **not needed** and is dropped from the plan.
(b) The built D3OneHot cell one-hot family need **not** be part of Φ. Its `[LIB]` section stays in use (D3Acc reuses it). C5 therefore has five families to satisfy:
update, S-def, shift, init, accept.

### Item 3: the generator (D3Acc.lean, EXPLORATORY, not a root, imports `Sit`)

* `accFam L n1 ac k1 ea T H` (layout level); **`accFamily_eq`**: `E.accFamily acc T H = accFam E.layout E.A0 E.acode (E.kc k₁) (E.enc k₁ acc) T H`, **by `rfl`**.
* Machine `prog` / **`accTM : FinTM2`** (finite labels: `GL n1 g` with `Fin` fields, `deriving Fintype`). Counters compute `HG = H·g`, `W`, `TW = T·W`,
  `V = (T+1)·W`, `CB = T·W + A + k1·H·g`. The `u` and `x` loops are **label chains**, because `n1` and `g` are constants. Each clause is the one-literal case
  of D3OneHot's literal routine, with a per-kind base counter (`AK.bc`: `TW` for code clauses, `CB` for cell clauses).
* **`acc_run`**: from `T`, `H` (unary) it reaches `done` within `accBound` steps, with exactly `encodeCNF (accFam …)` prepended. Hypotheses: `n1 ≤ A`, `k1 < KK`, `0 < H`.
  **`acc_time`**: within `accC L n1 k1 · (T+H+1)^4`, `accC = 314 · (A+KK+g+n1+k1+1)^5`. The constant 314 is exact (`example … = 314 := rfl`).
  **`acc_gen_time`**: the instance for a real `M`/`E`/`acc`, with only `0 < H` left.
* Degree `(T+H+1)^4` (vs `^5` D3Fam, `^6` D3OneHot/D3Shift): row `T` only, so there is no time loop, only `|clauses| · V`.

Fix rounds: Sit block 2 (an implicit-argument witness in `fam_pos`; `by decide` on a goal with free variables → `Nat.zero_le _`), after which it was clean. D3Acc: 4, none mathematical:
`cases c <;> decide` with a free variable; missing `(L := L)` annotations; `codeStart_run` started at var `v` while the `n1 = 0` case cannot change var
(stated with `false`); a looping `simp` lemma (the cell-offset equation holds by `rfl`); `rw [hg]` under a dependent label type; and a heartbeat timeout because the
precomputation's cost goal was too big inside `acc_run`, which was split out as `pre_run`. Then the bound needed explicit `(n1 := n1) (k1 := k1)`.

### Item 5: line counts

**Sit.lean 1943 → 2348 (+405: the 403-line block below plus 2 header-docstring lines), CRLF kept:**

| part | lines | category |
|---|---|---|
| faithfulness library (`Faithful`, `clauseSat_iff`, `faithful_*`, `Inc.ge`, `sat_allTrue`, `lt_numVars`) | 88 | **new library** (C5 will use it) |
| D3 families faithful (`fam_pos`, `sh_pos`) | 39 | new library (generic in the tables) |
| `Enc` helpers + `upd_pos`/`sdef_pos`/`shift_pos` | 32 | library / instantiation |
| `init_pos` | 46 | family-specific (init), item 2 |
| accept family defs + `acc_ok` + `unit_pol` + `acc_code`/`acc_cell` | 49 | **accept, family-specific** |
| `Accepts`, `accept_sound`, `unsat_of_noAccept` | 59 | **accept, C6 semantics** |
| `trans_allTrue`, `A0_two`, `accFamily_allTrue` | 34 | accept, all-true witness |
| repo link (`runI_*`, `runI_haltList`, `accepts_haltList`) | 53 | **A plumbing (new library)** |
| section header | 3 | |

**D3Acc.lean (new, 589):**

| part | lines | category |
|---|---|---|
| header doc | 28 | |
| spec (`codeLits`, `cellLits`, `accFam`) | 19 | family |
| machine (counters, kinds, labels, `litP`, `prog`, `accTM`) | 142 | family |
| one clause (`lit_run`, `encodeClause_unit`, `clause_run`) | 89 | family |
| chains + precomputation + `acc_run` | 209 | family |
| **time bound** (`accBound_mono`, `accBound_uni`, `accC`, `accBound_le`, `acc_time`) | 78 | **time bound** |
| link to `Sit` (`accFamily_eq`, `acc_gen_time`) | 25 | family |
| **new library** | **0** | D3OneHot's `[LIB]` sufficed (`emitS`, `copyS`, `mulS_run`, `gapS`, `drainS`, `xferES`, `bud_st`) |

**Comparison.** Generator: about 510 family + 78 bound. The built generators: D3Fam ≈ 600 + 145, D3OneHot ≈ 626 + 146, D3Shift ≈ 990 + 177, S-def 133 (an instance).
So accept is the cheapest non-instance generator, but it is **above the 200–400 P6 band** I had given it. The cost is not the clauses. It is the
precomputation (`pre_run`, 13 primitive steps) and the two label chains plus the empty-chain cases, which every generator pays. Semantics: accept's C6
part is about 0.14k (defs + forcing + `accept_sound` + `unsat`). That is at the top of the 0.09k–0.14k per-family C6 forcing band and below init's 0.17k. Like init, accept has both
characters: a C6 forcing lemma (cheap) plus a D generator (the real cost). Unlike init, its generator needed **no new primitive**.

### Checks (run this session, output quoted)

* `lake build` (final, after the header edit): `✔ [1263/1264] Built Sit (86s)` / `Build completed successfully (1264 jobs).` The only warnings are the three existing
  `declaration uses 'sorry'` (Challenge.lean:3:8, CookLevin.lean:803:8, SatInP.lean:15:8).
* `lake env lean D3Acc.lean`: no output (no errors, no warnings).
* `#print axioms` (ScratchAcc.lean, `import Sit`; D3Acc via a temporary copy with prints appended, since deleted): **all 87 new declarations** ⊆
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. E.g. `accept_sound`, `unsat_of_noAccept`, `trans_allTrue`, `accFamily_allTrue`, `init_pos`,
  `clauseSat_iff`, `acc_run`, `acc_time`, `acc_gen_time` → `[propext, Classical.choice, Quot.sound]`. `runI_haltList`, `accFamily_eq`, `Accepts`,
  `accFamily` → `[propext, Quot.sound]`. `Faithful`, `FamOK`, `iterate_bind_none`, `prog`, `accBound` → no axioms.
* Banned-token scan of Sit.lean, D3Acc.lean, ScratchAcc.lean: `no hits`.

### Lakefile (printed, NOT applied; needs your approval)

```
-roots = ["Challenge", "Comp", "CookLevin", "SatInP", "Solution", "Prog", "D3Fam", "D3OneHot", "D3Shift", "Sit"]
+roots = ["Challenge", "Comp", "CookLevin", "SatInP", "Solution", "Prog", "D3Fam", "D3OneHot", "D3Shift", "Sit", "D3Acc"]
```
D3Acc imports only `Sit`.

### New obligations recorded (none blocking)

* **A:** `hacc : ∃ i, E.dec M.k₁ i = acc` for `acc = inv true`. `Enc.ofFinTM2`'s `k₁` alphabet is the pushed symbols (plus the input alphabet if `k₁ = k₀`).
  If the verifier never outputs `true` that can fail, so A should add `acc` to the `k₁` alphabet of the `Enc` it uses (a small change to `ofFinTM2`, or a variant).
* **A:** `T ≥` the verifier's time bound `p(|x| + |y|)` for every `|x ++ y| ≤ m`, so that `runI_haltList` applies (monotone `p`, `T := p(m)`).
* **D (init generator):** emit I4's `Ys` codes sorted and deduplicated (`Inc` is needed by `encodeClause_denseClause`).
* **C5:** the five families only (no one-hot), with `clauseSat_iff` + `FamOK` (now proved for all five) as the clause semantics.

### Updated P6 estimate (supersedes the 2026-10-01 init table)

| Block | Estimate | Basis |
|---|---|---|
| **D total** | **≈ 6.6k–7.85k** (was 6.55k–8.25k) | remaining-D line was "label/state one-hot 350–600; accept 200–400; init 600–1000". Now: one-hot **dropped** (unneeded); accept **measured 0.59k** (over its band); init + input decoding 600–1000 **unbuilt** |
| A (plumbing) | 250–450, **0.05k done** (`runI_haltList`, `accepts_haltList`) | plus the two new obligations above (small) |
| **B** | ≈ 0.74k, DONE | measured |
| C (tableau semantics) | 2.8k–4.7k unchanged; C6 **≈ 0.79k done** (0.65k + accept 0.14k); **C6 complete for soundness**; C5 has its clause-semantics library (≈ 0.2k, faithfulness) | |
| **Total** | **≈ 10.4k–14.0k lines** (was 10.4k–14.4k) | the one-hot saving outweighs the accept overrun at the top end |

### What now stands between the current state and C5

Soundness chain (assignment ⇒ accepting real run) is **complete at the Sit level** and conditional only on clause hypotheses plus `|x| ≤ m` and `hacc`.
Before C5 can *start*, nothing is missing. All five families exist as Lean definitions, and their literal lists are proved faithful. C5's statement is:
for `y ∈ Ys*`, `|x++y| ≤ m`, with the real run accepting at row `T`, the exact one-hot image of the run (with `S[t,i]` := "row `t` is in situation `i`" and row-0
situation block false) satisfies update, S-def, shift, init and accept. What remains for the whole Cook–Levin hardness proof after C5: the **init
generator** (D, the one remaining new primitive: input symbol into label), **assembling the five generators into one machine plus decoding
`w`/computing `T`, `H`, `m`** (D2/D4/D5), and **block A** plumbing (verifier ⇒ `M`, `x`, `Ys`, `m`, `T`; `hacc`; `TM2OutputsInTime` ⇒ `runI_haltList`).
So the answer to "only C5 and block A?" is **no**. The init generator and the generator assembly (D) also remain. They do not block starting C5.

Not started, as instructed: C5. Status: **NOT PROVED**. `sat_in_p` (the open problem) is untouched, and Cook–Levin hardness is still `sorry`.

# C5: COMPLETENESS, THE RUN'S ASSIGNMENT SATISFIES ALL FIVE FAMILIES (2026-10-01, third): statement written BEFORE any proof

## Lakefile

The approved diff (D3Acc added to the roots) is applied. `lake build`: `✔ [1264/1265] Built D3Acc (99s)`, `Build completed successfully (1265 jobs).`
The only warnings are the three existing `declaration uses 'sorry'` (Challenge.lean:3:8, CookLevin.lean:803:8, SatInP.lean:15:8). C5 goes at the end of Sit.lean `[C6]` (a root), with no further lakefile change.

## Item 1. The target, stated precisely

**Data.** `M : FinTM2`, `E : Enc M`, input prefix `x : List (M.Γ M.k₀)`, allowed certificate symbols `Ys`, bounds `m`, `T`, output symbol
`acc : M.Γ M.k₁`, and a certificate `y` with
* (Y1) `∀ z ∈ y, z ∈ Ys`, (Y2) `(x ++ y).length ≤ m`, (Y3) `Accepts M (runI M (initList M (x ++ y)) T) acc`.
Write `H := capH m T (depth M)`, `V := E.layout.numVars T H`, `r t := runI M (initList M (x ++ y)) t`.

**The assignment** (`Enc.runAsg s T H`, `s = x ++ y`): `a := (List.range V).map (fun p => decide (Lit p))` (classical decide), where
`Lit p` holds iff, for some row `t`:
* `p = xIdx H t (code (r t))` (the real (label, state) code of row `t`), or
* `p = cIdx H t k j (cell (r t) k j)` for some `k < KK`, `j < H` (the real cell, ⊥ = code 0 included), or
* `t = t' + 1` and `p = xIdx H t (sa (sitIdx (r t')))` (`S[t', i]` is true exactly for the real situation of row `t'`). The row-0 situation block is all false.
So `a` is the **exact one-hot image of the real run**: in each code block and each cell exactly one literal is true, and exactly one situation literal per row `≥ 1`.

**Target theorem (`Enc.accept_complete`):** under (Y1)-(Y3) and `x` arbitrary, with no `|x| ≤ m` or `hacc` hypothesis expected to be needed,
`cnfSat` of all five families holds for `a` at `H = capH m T (depth M)`:
update `D3Fam.family layout la na wa T H N`, S-def `D3Fam.family layout la sa wa T H N`, shift/overflow/pushed fill `D3SH.shFamily layout sa pl cn pu N T H`,
init `initFamily x Ys m T H` and accept `accFamily acc T H`. Also `a.length = V`.
**Corollary (`Enc.five_iff`):** with `|x| ≤ m` and `hacc` (needed by soundness only), the five families are jointly satisfiable
⟺ `∃ y` with (Y1)-(Y3). This is `accept_sound` together with `accept_complete`.

**Per-clause route.** Use `clauseSat_iff` (needs `Faithful` for the *specific* literal list, re-derived per clause from the same facts as `upd_pos`/`sh_pos`/`init_pos`).
Exhibit one literal `(p, b)` of the list with `val p = b`:
* **positive literals** are true by the definition of `Lit` (a witness).
* **negative literals** need `¬ Lit p`, i.e. **index inversion**: `xIdx`/`cIdx` positions are injective, and code / situation / cell offsets are disjoint.
  This is the C5-only cost flagged in the C6 sessions. The forcing direction never needed it.
* **update/S-def clause `(t, i)`**: if `i = sitIdx (r t)`, the positive head is true (update: `na (sitIdx c) = code (stepI c)` by `table_agree`; S-def: by the definition).
  If `i ≠ sitIdx (r t)`, some body literal is false. This needs **situation injectivity**: `i < N`, `la i = code c`, and all window digits equal ⇒ `i = sitIdx c`.
  Not proved yet (`mix_sit`/`sit_surj` give existence only).
* **shift / overflow / pushed fill**: if `i ≠ sitIdx (r t)`, `¬S[t,i]` is false. Otherwise the target cell of row `t+1` equals `tabRow` (`table_agree`), and for in-range `u, x`
  either `x ≠` the source cell (the first negative literal) or the target equals `x`.
* **init**: the real start config `initList (x ++ y)`: I1 code, I2 empty stacks, I3 `x`, I4 `y[i] ∈ Ys` or ⊥, I5 (if `j < |x++y|` the cell is `enc z ≥ 1`, so `¬Z[j]` holds),
  I6 `j ≥ m ≥ |x++y|`.
* **accept**: (Y3) gives `code (r T) = acode` and top of `k₁` = `enc acc`. The negated units are false by exactness of the one-hot image.

**Expected asymmetry (prediction, to be checked):** forcing used positive literals only. Completeness needs (a) index inversion and (b) situation injectivity, both new,
and (c) heights `≤ H − d` on every row `t < T` to apply `table_agree` (already available as `capH_height`). Prediction: harder than any single forcing lemma
because of (a)+(b), but no new *mathematical* obstacle, since `a` is an exact one-hot image of a real run that `table_agree` already describes.

**Forward note (I4 sorting trap, not fixed now):** the *init generator* must emit I4's literal list `Z j :: Ys.map (cIdx … ∘ enc)` sorted and deduplicated
(or prove `denseClause` equal to the sorted version), because `encodeClause_denseClause` needs `Inc`. C5 uses the *specification* `initFamily`, whose
I4 is faithful even unsorted (`init_pos`), so C5 is not affected.

## Results (same session, checked against the statement above)

**The target is proved as stated.** `Enc.accept_complete` (Sit.lean, block `[C5]` at the end of `[C6]`): from `y ∈ Ys*`, `|x ++ y| ≤ m` and
`Accepts M (runI M (initList M (x ++ y)) T) acc`, the assignment `runAsg (x ++ y) T (capH m T (depth M))` has length `numVars` and satisfies update,
S-def, shift/overflow/pushed fill, init and accept. As predicted, it needs neither `|x| ≤ m` nor `hacc`.
**`Enc.five_iff`**: with `|x| ≤ m` and `hacc` (soundness's hypotheses), the five families are jointly satisfiable ⟺ some `y ∈ Ys*` with `|x ++ y| ≤ m` makes
the real run accept at row `T`. It is `accept_sound` + `accept_complete`, 19 lines.

The assignment is as specified: `RunLit s H p` (three disjuncts: code / cell / situation-in-next-row), `runAsg := (range V).map (decide ∘ RunLit)` (classical).
Clause semantics: `sat_run`, which is `clauseSat_iff` + "one literal of the list agrees with `RunLit`".

### Item 2: family by family, forcing reused "in reverse" or new work?

| family | lines | reused from the forcing direction | new work |
|---|---|---|---|
| shared: index inversion | 53 | nothing | **new**: `row_pos_inj` (div/mod), `xIdx_inj`, `xIdx_ne_cIdx`, `cIdx_inj`, `cell_off_lt`. The C6 sessions predicted this C5-only cost. |
| shared: situation injectivity | 41 | `sitIdx_spec` (the other half) | **new**: `sit_inj` via `mod_pow_eq_of_digits` (`Nat.mod_pow_succ`) + `Nat.mod_add_div` |
| shared: assignment + readback | 74 | `run_good`, `cell_lt`, `sitIdx_spec` | `RunLit`, `runAsg`, `sat_run`, `lit_x`/`lit_c`/`lit_s` (exactness of the one-hot image) |
| update + S-def | 69 (one generic `fam_complete` 55 + 7 + 7) | `table_agree_run` (code of row `t+1` = `na`), `lits_inc` (faithfulness), `litPos` arithmetic as in `fam_force` | the off-situation case: `la i ≠ code` ⇒ literal 0 false; otherwise `sit_inj` yields a window digit that differs ⇒ literal `k·d+j+1` false |
| shift / overflow / pushed fill | 65 | `table_agree_run` + `tabRow` case split (same as `sh_hold`/`ov_hold`/`pf_hold`), `inc_drop`/`*Pos_mono` (faithfulness, copied from `sh_pos`) | off-situation: `¬S` false via `lit_s`; in-range: case `x = source cell` (head true) or not (first literal false) |
| init | 121 (`init_complete` 105 + helpers) | `initList_k₀`/`_ne`, `cell_kc`, faithfulness copied from `init_pos` | the real start row read cell by cell. I5 needs `enc z ≥ 1` (`input_mem` + `enc_dec`), a negative literal |
| accept | 23 | `Accepts` unpacked as in `accept_sound` | negated units false by `lit_x`/`lit_c` |
| assembly + `five_iff` | 39 | `capH_height`, `depth_le_capH` | none |

**Verdict.** No family's satisfaction came from a forcing lemma run backwards. The forcing lemmas (`fam_force`, `sh_force`, `pf/ov_force`, `init_row0`, `acc_code/cell`) are
not used at all in C5. What was reused is the layer *under* them: `table_agree_run` (B1), `sitIdx_spec`, `run_good`, `tabRow`'s case split, and the
faithfulness facts. Each family needed a new but routine case split: "is this clause about the real situation?" Yes ⇒ the head literal is true by B1.
No ⇒ some negative literal is false by exactness.

### Item 3: the forcing vs. completeness asymmetry, checked

**There was an asymmetry, and it was mild. Completeness was not harder in kind.** Concretely:
* C5 needed two facts the forcing direction never touched: **index inversion** (positions are injective, blocks disjoint; 53 lines) and **situation injectivity**
  (`sit_inj`, 41 lines). Both are elementary `ℕ` arithmetic (div/mod, mixed radix). Neither needed a new idea or any change to an existing definition.
* Exactness of the one-hot image is used for negative literals only. The positive invariant of C6 was "true literals ⊇ real literals". C5 needs "= real literals".
  That holds by construction of `runAsg`, so no induction is needed (`RunLit` names the real run directly, rather than propagating row by row).
* No hidden gap surfaced. Every clause of every family is satisfied by the real run's image at `capH`. In particular:
  (i) the overflow/pushed-fill/in-range split at `capH` matches `tabRow` exactly (the same `region_cover` arithmetic);
  (ii) I5 (prefix form) holds because real cells are never code 0;
  (iii) accept's negated units hold because the image is exactly one-hot.
* The one place where completeness *could* have failed is a lost literal (out of range / shadowed). `FamOK`/`clauseSat_iff` (last session) already excluded that, and C5
  re-derived faithfulness per clause from the same `lits_inc`/`inc_drop`/`init_pos` facts (copied, ~15 lines in total).
* Risk named in P5 (forcing easy, completeness hard): **not realized** at the Sit level. C5 cost 0.49k against the soundness side's ≈ 0.79k (C6) + 0.2k (faithfulness).

Fix rounds: 4, none mathematical: an implicit argument of `row_pos_inj`, `simp` needing `Nat.mod_one`, a metavariable index into `mem`, a `show` stating
`depth M` vs `E.layout.d`, `subst` ordering in the shift branches, and a `rw [← h0]` that rewrote every `0` (fixed with `rwa … at`).

### Item 4: forward note (I4 sorting trap), unchanged and not fixed

The init *generator* must emit each I4 clause's literal list sorted and deduplicated, or prove `denseClause` equality with the specification's unsorted list
(all literals are positive, so `lookup` agrees). C5 was proved against the specification `initFamily`. So if the generator is linked by
`denseClause` equality (as `accFamily_eq` is for accept), `accept_complete` transfers unchanged.

### Item 5: line count

Sit.lean **2348 → 2838 (+490**: 488-line block `[C5]` + 2 header-docstring lines), CRLF kept. No other Lean file changed. `ScratchC5Ax.lean` (axioms checker, scratch, not a root) is new.
The development scratch `ScratchC5.lean` is deleted (it would now clash with Sit).

| part | lines | category |
|---|---|---|
| index inversion (`Layout`-generic) | 53 | **new library** (C5-only) |
| situation injectivity | 41 | new library (C5-only) |
| assignment, `sat_run`, readback | 74 | C5 core |
| update + S-def | 69 | per family |
| shift / overflow / pushed fill | 65 | per family |
| init | 121 | per family |
| accept | 23 | per family |
| `accept_complete`, `five_iff` | 39 | assembly |
| section header | 5 | |

**Comparison.** C5 total 0.49k for all five families (≈ 0.17k shared + ≈ 0.28k per-family + 0.04k assembly). Against the forcing lemmas: C6 forcing was ≈ 0.09k–0.14k
per family plus ≈ 0.15k of propagation (depth_cover, induction). C5's per-family cost is ≈ 0.02k (accept) to 0.12k (init), the same order. Its shared cost (inversion +
injectivity) is the asymmetry, and it is small. Against the generators (D: 0.59k for accept, 0.6k–1.2k each for the others, plus their time bounds), C5 is
**far cheaper**: about one generator's worth of lines for all five families. In character it resembles C6 (structural case splits, `omega`, no machine
runs). It is unlike D, which is long step chains and cost budgets.

### Item 6: checks (run this session, output quoted)

* Lakefile diff applied (approved): `roots = [..., "Sit", "D3Acc"]`. First `lake build`: `✔ [1264/1265] Built D3Acc (99s)` / `Build completed successfully (1265 jobs).`
* `lake build` after C5 (build_c5.log): `✔ [1263/1265] Built Sit (29s)`, `✔ [1264/1265] Built D3Acc (42s)`, `Build completed successfully (1265 jobs).` The only warnings are the three
  existing `declaration uses 'sorry'` (Challenge.lean:3:8, CookLevin.lean:803:8, SatInP.lean:15:8).
* `#print axioms` (ScratchC5Ax.lean, `import Sit`) on all **30** new declarations: every one ⊆ `[propext, Classical.choice, Quot.sound]`. E.g.
  `accept_complete`, `five_iff`, `init_complete`, `shift_complete`, `fam_complete`, `sit_inj`, `runAsg` → `[propext, Classical.choice, Quot.sound]`;
  `row_pos_inj`, `xIdx_inj`, `cIdx_inj`, `RunLit`, `lit_cell0` → `[propext, Quot.sound]`; `cIdx_split` → `[propext]`. No `sorryAx`.
* Banned-token scan (sorry/admit/axiom/native_decide/decide +native/implemented_by/@[extern]/unsafe/partial/open private/set_option debug/run_cmd/addDecl)
  on Sit.lean, ScratchC5.lean (before deletion), ScratchC5Ax.lean: `no hits`.

### Item 7: does soundness + completeness now hold for the formula?

**At the Sit (specification) level: yes, both directions are proved.** `five_iff` is a biconditional between joint satisfiability of the five
specified families (at `H = capH`) and the existence of an accepting certificate `y ∈ Ys*` with `|x ++ y| ≤ m` at row `T`. Its only hypotheses are `|x| ≤ m` and
`hacc`.

**Real gaps that remain for Cook–Levin hardness (none at the clause-semantics level):**
1. **D: init generator** (unbuilt; new input-symbol-into-label primitive for I3; I4 sorted/dedup + `denseClause` equality).
2. **D: assembly** (D2/D4/D5): one machine emitting the five families' concatenation from the instance `w`, computing `T`, `H`, `m`, with a polynomial time bound,
   plus `encodeCNF`-of-concatenation = concatenation of the families. The five generators exist separately: D3Fam (update, S-def via D3SDef instance), D3Shift, D3Acc. S-def's
   D3SDef is still **not a root**.
3. **A: plumbing**: the verifier of an NP language ⇒ `M`, `x = map inv (map inl (ea w) ++ [inr none])`, `Ys = image of inv ∘ inr ∘ some` (certificates are *all*
   strings over `Γ₁` with the identity encoding, so every `y ∈ Ys*` is a genuine certificate encoding, as checked in Millennium.lean), `m = |x| + p(|w|)`, `T ≥` the verifier's
   time bound on every `|x ++ y| ≤ m`. Also `hacc` (`acc` in `Enc`'s `k₁` alphabet, needs a variant of `ofFinTM2`), and `TM2OutputsInTime` ⇒ `Accepts` via `runI_haltList`/`accepts_haltList`
   (both directions; soundness also needs `inv` injective to read `b = true`).
4. Then `cook_levin` itself (currently `sorry`) = A + D assembled against `five_iff`.

### Updated P6 estimate (supersedes the 2026-10-01 accept table)

| Block | Estimate | Basis |
|---|---|---|
| D total | ≈ 6.6k–7.85k (unchanged) | built ≈ 5.15k (Prog 958, D3Fam 1088, D3OneHot 1005 (its `[LIB]` is used), D3Shift 1375, D3SDef 137, D3Acc 589); remaining: init generator 0.6k–1.0k + assembly |
| A (plumbing) | 250–450, 0.05k done | unchanged |
| B | ≈ 0.74k, DONE | measured |
| **C (tableau semantics)** | **≈ 1.7k–1.9k, essentially DONE** (was 2.8k–4.7k) | measured: C1+C2 ≈ 0.19k, C6 ≈ 0.79k, faithfulness ≈ 0.2k, **C5 0.49k**. Slack 0–0.2k for linking the assembled generator's output to `five_iff` |
| **Total** | **≈ 9.3k–11.2k lines** (was 10.4k–14.0k) | C band replaced by its measurement; no other band changed |

Remaining work ≈ 1.65k–3.3k lines (D remainder + A + C slack), roughly 2–5 sessions at the recent pace. This covers **Cook–Levin hardness only**. `sat_in_p` (part (d),
the open problem) is untouched and has no approach. Status: **NOT PROVED**.


---

# INIT GENERATOR (D3Init.lean): TARGET, stated before any code (2026-10-01, fourth session)

## What must be emitted

The generator must emit **exactly** `Sit.Enc.initFamily x Ys m T H`, the six sub-families I1-I6 of the 2026-10-01 init session,
in that order (`initCode ++ initOther ++ initIn ++ initCert ++ initPre ++ initTail`), each clause a dense clause over
`layout.numVars T H`, encoded with the real `SATDef.encodeCNF`.

**I4 is emitted sorted and deduplicated** (the forward note, unchanged since it was logged): each I4 clause is emitted from the literal list
`(Z j, true) :: ycs.map (fun c => (cIdx H 0 k₀' j c, true))`, where `ycs` is the strictly increasing list of the distinct codes
`enc k₀ z`, `z ∈ Ys` (`Finset.sort` of the image finset). `Inc` then holds (codes are `≥ 1`, so `Z j = code 0` comes first), as
`encodeClause_denseClause` requires.

## Layout-level statement (what D3Init proves)

* `D3Init.initFam L ic k0 ycs xs m T H : CNF`, a pure specification parametric in the layout `L`, the start code `ic`, the input stack
  index `k0`, the I4 code list `ycs`, and the input codes `xs : List (Fin L.g)`.
* A generator machine `iprog` (finite labels; a genuine `FinTM2`, `initTM`) over the counter stacks of D3OneHot's `[LIB]` **plus one
  input stack over `Fin L.g`** that holds `xs.reverse`. Its input counters are `T`, `n = |xs|`, `e = m - n`, `f = H - m`, all unary.
  (Taking the differences as inputs avoids a subtraction primitive. Block A/assembly must supply them; at `H = capH`,
  `f = (T+1)·d + 1`.)
* `init_run` / `init_time`: from the start configuration the machine reaches `done` within `initC · (T+H+1)^p` steps, with
  `encodeCNF (initFam … (n+e) T (n+e+f)) ++ o` on the output stack. Hypotheses: `ycs` sorted with `0 < c < g`, `k0 < KK`,
  `ic < A`, `0 < f` (I5's literal `Z (j+1)` must be in range: `m < H`, true at `capH`).

## What "the C5 result carries over unchanged" requires, precisely

A Lean **equality of CNFs** (`List Clause`), `initFamily_eq`:

`E.initFamily x Ys m T H = D3Init.initFam E.layout (E.lc (some M.main, M.initialState)) (E.kc M.k₀) (E.ycs Ys) (x.map E.encF) m T H`.

I1, I2, I5 and I6 should match up to `List.length_map`. I3 matches by `getElem?_map`. I4 is the only real content: for each `j`, a
`denseClause` equality between the specification's unsorted, possibly duplicated list and the sorted, deduplicated one. The lemma
for that is `denseClause_congr`: two all-positive literal lists with the same set of positions have the same
`denseClause`, because `denseClause` is pointwise `lookup`. With `initFamily_eq`, `five_iff` (stated for `initFamily`) applies to the
generator's output by `rw`, with **no new semantics**. The generator output is then `encodeCNF (E.initFamily x Ys m T H) ++ o`.

## The new primitive, flagged as unmeasured, to be built first

(P1) The other generators' machines have only unit counters and one `Bool` output (D3OneHot `SK`/`SΓ`). Reading `x` needs a stack whose
symbols carry a code. Plan: a stack type `IK C = base (SK C) | inp` with `inp`'s alphabet `G`; a statement lift `liftS`
(`stepAux_liftS`, the Comp.lean `stepAux_lift` pattern), and a **run-lifting** theorem: any `RunLe` of the base counter machine
ending at a live label lifts to the extended machine with the input stack untouched. This keeps the whole D3OneHot `[LIB]` (and every
counter routine proof) usable verbatim.

(P2) The read step proper: label chain `rd i` (`i : Fin g`), one step each: `peek inp` tests `top = some i`; on a hit it pops and
jumps to the clause label carrying `i` (`e00 (inp i)`), otherwise it goes to `rd (i+1)`. The machine state stays `Bool`. Running
from `rd 0` on `c :: xs'` reaches `e00 (inp c)` in `c + 1` steps with `xs'` left.

## INIT GENERATOR: RESULTS (same session, checked against the target above)

**Built and proved: D3Init.lean (new, 1599 lines, EXPLORATORY, not a lakefile root, imports `Sit`).** The target statement held as
written, with one refinement. The input stack holds `Fin L.g` codes. The real-machine theorem takes `x.map encF` (`encF z = ⟨enc k₀ z, enc_lt …⟩`) reversed.

### Item 2: the new primitive (built first, as its own sections `[PRIM]`, lines 21–193, 173 lines)

* `IK C = b (SK C) | inp`, alphabet `IΓ C G` (`SΓ C` on base stacks, `G` on `inp`); `emb S xs` (stacks from base stacks + input).
* `liftS` (statement lift), **`stepAux_liftS`** (structural `Stmt` induction, exactly the Comp.lean `stepAux_lift₁` pattern),
  `Lifts M M'` (`M' l = liftS (M l)` or `M l = halt`), **`run_lift`** / `runLe_lift`: any run of the counter machine ending at a live
  label is a run of the extended machine with the input stack untouched. Labels where the base machine halts are free for the
  extended machine, and that is where the read tests live.
* `rdS` and **`read_run`**: the test chain `rd i` (`peek inp` sets the `Bool` state to `top = some i`; on a hit it pops and jumps to
  `hit i`, otherwise to `rd (i+1)`). From `rd 0` on `c :: xs` it reaches `hit c` in `c + 1` steps with `xs` left. The machine state stays `Bool`.

**Did it need new techniques beyond Prog.lean's D1 library and the other D3 generators? Partly, and they were cheap.** No D1 lemma
covers a stack whose symbols carry data, and no D3 generator reads anything but unary counters, so the stack type, `run_lift` and
`read_run` are new. The only technique in them, though, is structural induction on `Stmt` plus induction on `Run`. That is the
Comp.lean / block-B pattern already used twice in this project. The `[PRIM]` sections **compiled on the first attempt** (2 lint
warnings, fixed). The one real consequence was elsewhere. D3OneHot's `stLoop` requires the loop body to restore every stack, and
a body that pops the input does not. So the I3 loop is a direct induction in the extended machine (`i3_run`, 88 lines),
built from lifted counter segments + `read_run`. `run_lift` also lets every counter routine be proved in the plain counter machine with
the D3OneHot `[LIB]` verbatim (`copyS`, `mulS_run`, `gapS`, `drainS`, `stLoop`, …) and lifted afterwards. That is why the rest of the
generator reused the existing patterns unchanged. **Expected reuse:** `run_lift` is the embedding lemma the assembly needs
(running a generator inside a larger machine). It currently adds one stack; assembly needs a renaming into a larger union of stacks.
That is the same proof with a different `emb`.

### Item 3: the generator

* One generic clause routine for **all seven clause kinds** (`CL`: `code`, `inp c`, and phases `tail`/`pre`/`cert`/`o2`/`o1`), with
  **per-literal offset and sign** (`CL.off`, `CL.sg`; D3OneHot had one sign per clause). I4's literal chain over `ycs` is the offset
  table `(0 :: ycs).getD l 0` inside that routine. This is D3Shift's label-chain idea, folded into the literal loop.
* Five runtime loops via `stLoop` (one generic `phase_run`): I6 (`H−m` units), I5, I4 (`m−n` each), and **I2 split into two flat loops**
  (`q < k0·H` and `q < (KK−k0−1)·H`, flat index `q = k·H + j`). This avoids a runtime comparison with `k0`. It costs a reindexing lemma
  (`filter_ne_range`, `flat_blocks`, `enc_other`, ≈ 45 lines). The I3 loop (reads `x`) and the I1 unit clause come last.
* Precomputation (27 primitive steps, `pre_run`): `m`, `H`, `H·g`, `W`, `V`, five cell bases, two counts. The inputs are `T`, `n = |x|`,
  `e = m − n`, `f = H − m`. Taking differences avoids a subtraction primitive. **New assembly/A obligation:** supply these four unary
  counters and the reversed code list of `x` on a `Fin g` stack.

### Item 4: the C5 carry-over

* **`initFamily_eq`** (CNF equality, Lean `=`): `E.initFamily x Ys m T H = initFam E.layout (lc start) (kc k₀) (ycs E Ys) (x.map (encF E)) m T H`.
  I1, I2, I5 and I6 are `rfl` after `List.length_map`. I3 is `getElem?_map`. I4 is per clause **`denseClause_congr`** (all-positive lists with the
  same positions give equal dense clauses, via `lookup_pos`) plus `mem_ycs`. `ycs E Ys := (Ys.map (enc k₀)).toFinset.sort (· ≤ ·)` is strictly
  increasing (`List.sortedLT_iff_pairwise`, `Finset.sortedLT_sort`), and its codes are `≥ 1` (`enc_pos`, from `enc_dec`) and `< g` (`enc_lt`).
  `ycs` is a `noncomputable def` because `Enc`'s maps are classical. That is irrelevant for proofs.
* **`init_gen_time`** / **`init_gen_capH`**: the real machine's output is `encodeCNF (E.initFamily x Ys m T H) ++ o`, the **same CNF term**
  that `five_iff` quantifies over. At `H = capH m T (depth M)` the only hypothesis is `|x| ≤ m`, which `five_iff` also assumes. So `five_iff`
  applies to the generator's output by rewriting. No new semantics were needed.

### Item 5: time bound

`init_run`: explicit bound `initBound = preB + 6·loopB + clauseB` (I3's `n·bodyB + 1` is absorbed by one `loopB`). `initBound_mono` (gcongr),
`initBound_uni` (`linarith` with the 36 monomials `k^a y^b`, `a,b ≤ 5`, after `ring_nf`), `initBound_le`, and **`init_time`**:
`≤ initC · (T + H + 1)^5`, `initC = 18928·(A+KK+g+|ycs|+k0+1)^5`. The constant 18928 is exact (`example … = 18928 := rfl`). Degree 5 in
`T+H` matches D3Fam (5). D3OneHot and D3Shift are 6, D3Acc is 4.

### Item 6: line counts (D3Init.lean, 1599 total)

| category | lines | content |
|---|---|---|
| **new primitive `[PRIM]`** | **173** | stack type + `run_lift` (137), read chain (36) |
| family-specific `[FAM]` | 1200 + 129 | spec 43, machine + labels 249, literal positions + clause routine 211, phase loops 104, **I3 read loop 88**, kind lemmas 70, blocks = family 113, precomputation 148, whole generator 174; link to Sit (incl. `denseClause_congr`, I4 sort/dedup) 129 |
| time bound `[BOUND]` | 77 | |
| header | 20 | |

Comparison (family + bound): D3Fam ~600+145, D3OneHot ~626+146, D3Shift ~990+177, D3Acc ~510+78, **D3Init ~1330+77 (+173 primitive)**.
**Init is the most expensive generator, but the cause is not the new primitive.** The primitive plus the read loop are ≈ 260 lines and
were the smoothest part. The cost comes from the family's breadth: six sub-families, seven clause kinds, six loops, a 27-step precomputation
(148 lines; D3Acc's is ~60), and the output-equals-family layer (113 + 129 link lines). The other generators have one or two clause shapes.
The bound section is the cheapest so far (77), because loop costs are bounded uniformly by one `loopB`.

Fix rounds: about 20 compile rounds, **none mathematical**. They were implicit arguments not inferred (`ic`, `L`, `H`), `simp` orientation of `≠` facts
(`CB = p.cN` vs `p.cN = CB`), type ascriptions on `CL.inp c`, unreduced `preF … p.cZ` terms, a named `?S` hole that unification cannot
assign (fixed with `apply Exists.intro`), and one `ring` that worked only as `ring_nf` (made `ring1` + `congr 1`).

### Item 7: checks (run this session, output quoted)

* `lake env lean D3Init.lean`: exit 0, **0 warnings**.
* `#print axioms` (ScratchInitAx.lean in the session scratchpad, `import D3Init` via a scratch `.olean`) on **all 122** D3Init declarations:
  28 × `[propext, Classical.choice, Quot.sound]`, 26 × `[propext, Quot.sound]`, 24 × `[propext]`, 43 × "does not depend on any axioms",
  plus `init_gen_capH` → `[propext, Classical.choice, Quot.sound]`. Examples: `run_lift`, `read_run`, `stepAux_liftS` → `[propext, Quot.sound]`;
  `init_run`, `init_time`, `initFamily_eq`, `init_gen_time` → `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.
* Banned-token scan (sorry/admit/axiom/native_decide/decide +native/implemented_by/@[extern]/unsafe/partial/open private/set_option debug/
  run_cmd/addDecl) on D3Init.lean, ScratchGen2.lean, ScratchInitAx.lean: `no hits`. (The assembly was developed in a scratchpad file that
  imports a scratch D3Init `.olean`. No `sorry` was ever written into D3Init.lean.)
* `lake build` (build_init.log): `Build completed successfully (1265 jobs).` The only warnings are the three existing `declaration uses 'sorry'`
  (Challenge.lean:3:8, CookLevin.lean:803:8, SatInP.lean:15:8). D3Init is not a root yet. The proposed lakefile diff is in the session report, unapplied.

### Item 8: updated P6 estimate (supersedes the C5 table)

| Block | Estimate | Basis |
|---|---|---|
| D total | ≈ 7.75k–8.75k (was 6.6k–7.85k) | built ≈ 6.74k (Prog 958, D3Fam 1088, D3OneHot 1005, D3Shift 1375, D3SDef 137, D3Acc 589, **D3Init 1599**); remaining: assembly D2/D4/D5 **1.0k–2.0k** (implied 0.85k–1.7k before; raised because init came in at 1.6–2.7× its 0.6k–1.0k estimate, and assembly has the same "breadth" profile: a long precomputation plus stitching six generators) |
| A (plumbing) | 250–450, 0.05k done | unchanged; **plus the new interface obligations**: `|x|`, `m−|x|`, `H−m` unary and the reversed `Fin g` code list of `x` |
| B | ≈ 0.74k, DONE | |
| C | ≈ 1.7k–1.9k, DONE; slack 0–0.2k | |
| **Total** | **≈ 10.4k–12.0k lines** (was 9.3k–11.2k) | init measured |

Remaining ≈ 1.2k–2.6k lines (assembly 1.0k–2.0k + A 0.2k–0.4k + C slack), roughly 2–4 sessions. This covers **Cook–Levin hardness only**. `sat_in_p`
(part (d), the open problem) is untouched and has no approach. Status: **NOT PROVED**.


---

# STACK EMBEDDING (generalized `run_lift`) + ASSEMBLY START (2026-10-02): target written BEFORE any code

## Lakefile

D3Init added to `lean_lib` roots at the start of this session (diff approved in the user's message). Build result: see "Checks" below.

## What `run_lift` does today, and why it is not enough

`D3Init.run_lift` handles one fixed shape: stacks `IK C = b (SK C) | inp`, alphabet `IΓ`, the counter machine's stack `k` sent to `.b k` with the
*same* alphabet (definitionally), labels unchanged (`Λ' = Λ`), and the one extra stack `.inp` untouched. Assembly needs five generators side by side,
each written against its own local stack type:

| generator (instance) | stack type | alphabet | labels | start config | end |
|---|---|---|---|---|---|
| update (D3Fam, `na`) | `D3Fam.GK` (own inductive, `out | c CK`) | `GΓ` | `D3Fam.GL N nLits` | `pre .eg`, `D3Fam.st (initF T H) o` | `done` (halt) |
| S-def (D3Fam, `sa`) | same type as update, **second copy** | `GΓ` | same type, different program | same | same |
| shift (D3Shift) | `SK D3SH.CK` | `SΓ` | `D3SH.Lab L N` | `pre .eg`, `st (initF T H) o` | `done` |
| accept (D3Acc) | `SK D3Acc.CK` | `SΓ` | `D3Acc.GL n1 g` | `pre .eg`, `st (initF T H) o` | `done` |
| init (D3Init) | `IK D3Init.CK` (counters + input stack) | `IΓ CK (Fin g)` | `D3Init.GL g n` | `pre1 .eg`, `emb (st (initF T n e f) o) xs.reverse` | `done` |

All five use `σ = Bool`. Every end configuration in the time lemmas is `⟨some .done, v, S⟩` with `S` **existential except for `S .out`**: no
generator proves that its scratch counters are restored, or even that `Tn`/`Hs` still hold `T`/`H` at the end.

## The generalized target (`Emb.lean`, depends only on `Prog`)

Data of an embedding of a sub-machine (`K`, `Γ`, `Λ`) into a host (`K'`, `Γ'`, `Λ'`), same `σ`:

* `e : K → K'` **injective** (stack renaming);
* `ι : ∀ k, Γ k ≃ Γ' (e k)` (alphabet identification per stack; in every instance it is `Equiv.refl` after a case split, so no casts);
* `φ : Λ → Λ'` (label renaming; injectivity is NOT needed);
* `mapS e ι φ : TM2.Stmt Γ Λ σ → TM2.Stmt Γ' Λ' σ`: `push k f ↦ push (e k) (ι k ∘ f)`, `pop/peek k f ↦ pop/peek (e k) (fun s o => f s (o.map (ι k).symm))`,
  `goto f ↦ goto (φ ∘ f)`, `load`/`branch`/`halt` unchanged.
* `Embeds M M'` : `∀ l, M' (φ l) = mapS (M l) ∨ M l = .halt` (the host may do anything at the image of a halting label: that is where the next
  generator is chained in).

Relations between stack families (no function on host stacks is defined, so no dependent `if`):

* `Agree S S'` : `∀ k, S' (e k) = (S k).map (ι k)` (the host holds the sub-machine's stacks on the image of `e`);
* `Frame S' S''` : `∀ k', (∀ k, e k ≠ k') → S'' k' = S' k'` (host stacks outside the image are unchanged).

**Target `run_embed`.** If `Embeds M M'`, `Run M n ⟨l, v, S⟩ ⟨some l', v', T⟩` and `Agree S S'`, then there is `T'` with
`Run M' n ⟨l.map φ, v, S'⟩ ⟨some (φ l'), v', T'⟩`, `Agree T T'` and `Frame S' T'`. Same step count `n`, so `runLe_embed` (same bound `B`) follows.

**What is preserved and why the observable behavior is the same.** The observable of a generator is its output stack. Each generator's `out` is sent by `e`
to the host's single shared output stack, with `ι = refl`; `Agree` at `k = out` gives host `out` = sub-machine `out` *exactly* (`map id`). So if the
sub-run ends with `S .out = encodeCNF F ++ o`, the host's output ends as `encodeCNF F ++ o` too. Why the run is the same, step by step: the host's
statement at `φ l` is `mapS (M l)`; each `push/pop/peek` touches only `e k`, whose contents are the image of `S k` under the bijection `ι k`, so the
popped/peeked value read back through `ι.symm` is exactly what the sub-machine reads (state update identical), and the push writes the image of what the
sub-machine writes (`Agree` re-established). Injectivity of `e` is what makes an update at `e k` leave every other `e k₂` (and so `Agree` at `k₂`) intact;
`Frame` holds because only stacks `e k` are ever written. Labels are renamed pointwise by `φ`; a halting label is never stepped *from* inside a run
that ends live (the run lemma ends at `some l'`), exactly as in `run_lift`.

**Sanity instance (must be proved, as the evidence that this generalizes `run_lift`):** `run_lift` is `run_embed` with `e = IK.b`, `ι = refl`, `φ = id`,
reconstructed in `Emb.lean`'s user file without editing D3Init.

## Assembly design this embedding commits to (stated now, so a wrong choice is visible)

* Host stacks: one shared `out : Bool`, one input-code stack `inp : Fin g` (only init's `.inp` maps there), and **private, disjoint counter blocks**
  per generator instance (`upd x`, `sdf x` for two copies of `D3Fam.CK`, `sh x`, `ac x`, `ini x`), plus the precomputation's own counters.
  Private blocks are forced by the existential end states: no generator returns its counters, so none can be shared without proving restoration
  for all five (a new obligation per generator, not budgeted).
* Each generator instance therefore needs its private block **preloaded** before it runs: `Tn = T`, `Hs = H` (init: `Tn, Xn, En, Fn = T, |x|, m-|x|, H-m`),
  all other private counters 0. Loading all blocks happens in the precomputation (D2) before any generator runs; afterwards the generators run in
  sequence and each one only reads its own block (`Frame` keeps the others intact).
* Output order: each generator prepends, so running G1..G5 in sequence leaves `encodeCNF F5 ++ ... ++ encodeCNF F1 ++ o`; `encodeCNF` is `flatMap`,
  so this is `encodeCNF (F5 ++ ... ++ F1) ++ o`; `cnfSat` of a concatenation is the conjunction, order irrelevant for `five_iff`.

## Structural risks to check (and flag immediately if they occur)

1. A generator referring to a stack other than through `TM2.Stmt` constructors (e.g. stack-dependent lemmas the run proofs need about *host* stacks). Expected: none; run lemmas are about `prog` only.
2. D3Fam's `GK` is a separate inductive from `SK D3Fam.CK`: harmless for `run_embed` (any `K`), costs one more `e`.
3. The two D3Fam instances share one label type but have different programs: they need two different host label constructors; `φ` differs.
4. Label types must stay `Fintype` in the host (`FinTM2`): host label inductive over the five label types.
5. `D3SDef` is still not a root; the S-def instance is used through `D3Fam.gen_time` + `D3SDef.sdFamily_eq`.

## STACK EMBEDDING + ASSEMBLY: RESULTS (same session, checked against the target above)

### Item 2: the embedding lemma. **Proved as stated. A straightforward generalization, with one structural change.**

`Emb.run_embed` / `runLe_embed` (Emb.lean, 179 lines, imports only `Prog`) are exactly the target above: same `n`, same bound, `Agree` at the end, `Frame`.
The proof skeleton is `run_lift`'s unchanged (induction on `n`; the halting-label case closed by `iter_none`; one `stepAux` lemma by induction on `Stmt`).
What is genuinely new is small but real:
* **Relational, not functional.** `run_lift` could write the host stacks as a function `emb S xs` of the sub-machine's stacks. With several sub-machines the host stacks
  outside the image are not a function of the sub-machine's, so the statement uses `Agree`/`Frame` and an existential end state. This is what makes the lemma
  reusable for five generators; it is also why no dependent `if` on host stacks was ever needed.
* **Injectivity of `e`** is used exactly once (`Agree.update`: a write to `e k` leaves `e k₂` alone).
* **Alphabet bijections** `ι`: reads go back through `ι.symm` (`Option.map`), writes through `ι`. In every instance `ι = Equiv.refl` after a case split; no casts anywhere.
Fix rounds: Emb 1 (a lemma name, `List.tail_map` → `← List.map_tail`).

**Sanity check (done, as required):** `Asm.run_lift'` re-derives `D3Init.run_lift` from `run_embed` (`e = IK.b`, `ι = refl`, `φ = id`; `mapS_liftE : mapS liftE id q = liftS q`,
end state recovered as `emb S' xs` by `funext` from `Agree` + `Frame`). 3 small fix rounds, all the same issue: `simp` does not rewrite `⇑(Equiv.refl α)` when the list's
type is only *definitionally* `α` (e.g. `IΓ C G (.b k)` vs `SΓ C k`); closed by `List.map_id` up to defeq.

### Item 5: did any generator's internal assumptions fail to survive re-embedding? **No. Nothing to stop for.**

Checked against the five risks listed in the target:
1. All five generators touch stacks only through `TM2.Stmt` constructors; `mapS` covers every constructor, and every run lemma is about the sub-program only. None of
   the five files was edited; their time lemmas are used verbatim (`upd_time`, `sdef_time`, `shift_time`, `acc_gen_time`, `init_gen_capH`).
2. D3Fam's separate `GK` (not `SK CK`): just another `e` (`eU`/`eS`). Harmless, as predicted.
3. Two D3Fam instances: two host label constructors (`HL.up`, `HL.sd`) and two private counter blocks; the `φ`s differ. Worked as predicted.
4. Finiteness: `hostTM : FinTM2` typechecks (`HK`, `HL` derive `DecidableEq, Fintype`).
5. Halting labels: besides `done`, several generators halt at `bad`, and D3Init's counter program halts at `rd _`. `Embeds`' halt exception covers all of them; the host
   chains only at `done` (`if l = .done`), and every other label is `mapS` of the sub-program's statement (`embeds_*` by `by_cases` + `rfl`).

**One forced design consequence (cost, not breakage), confirmed:** because every generator's end state is existential (no generator returns its counters), each
needs a **private** counter block **preloaded** before it runs. The precomputation therefore has to load 12 counters (`Tn, Hs` × 4 blocks; init: `Tn, Xn, En, Fn`)
plus the reversed codes of `x` onto `inp`, all other host counters 0. `Frame` is what carries each untouched block through the earlier generators (`seq_run`).

**Minor, checked:** `realProg` is `noncomputable` (via `D3Init.ycs`, a classical `Finset.sort`; `Enc.ofFinTM2` is classical anyway). Not a problem:
`PolynomialTimeReducible` is `∃ (f) (_comp : TM2ComputableInPolyTime …), …` (Millennium.lean:297), a `Prop`.

### Item 3: assembly. **Meaningfully underway; stopped at a clean boundary (the precomputation's postcondition).**

Asm.lean (437 lines, not a root):
* **`seq_run`** (generic in the five sub-programs): host stacks with each private block preloaded with that generator's start counters ⇒ the host runs
  init → update → S-def → shift → accept with one chaining step between them (`chain` resets the state bit to `false`, which every generator's start
  configuration requires), halts at `fin` within `Bi + Bu + Bs + Bh + Ba + 5`, output `wa ++ (wh ++ (ws ++ (wu ++ (wi ++ o))))`. **Compiled first try.**
* **`real_run`**: the same on the real generators of `M` (`realProg E Ys acc`), at `H = capH m T (depth M)`, assuming only `|x| ≤ m`: output exactly
  `encodeCNF (Phi E x Ys acc m T) ++ o`, where `Phi` is the concatenation of the five families of `five_iff`.
* **`phi_iff`**: `(∃ a, cnfSat (Phi …) a) ↔ ∃ y ∈ Ys*, |x ++ y| ≤ m ∧ Accepts M (runI M (initList M (x ++ y)) T) acc` (`five_iff` + `cnfSat_append`; needs `hacc`).

So D (assembly) is now joined to C: **the assembled machine's output formula is proved equivalent to acceptance**, conditional only on the precomputation's
postcondition (the preload hypotheses `ho hin cu cs ch ca ci` of `real_run`).

**Precise interface for the next step (D2, the precomputation)**: a host prefix that, from the host's real input, reaches `⟨some (.ini (.pre1 .eg)), false, S₀⟩` with
`S₀ .out = o`, `S₀ .inp = (x.map (encF E)).reverse`, every private block equal to `cnt () (initF …)` as in `real_run`, within a polynomial step bound. That needs:
which of `T`, `m`, `|x|` the host receives vs. computes (this is where D2 meets block A: `x`, `m`, `T` are functions of the instance `w`), multiplication for
`capH = m + (T+1)·d + 1` (D3OneHot's `mulS` exists), 12 counter copies (`xfer` with several targets exists), and adding `pc` stacks/labels to `HK`/`HL`
(the [SEQ] proofs case-split only on sub-machine stacks, so new host constructors should not break them, to be confirmed).

Not started, as instructed: block A plumbing.

### Item 4: line counts against the 1.0k–2.0k assembly estimate

| Piece | Lines | Note |
|---|---|---|
| Emb.lean (generic embedding) | 179 | 0.1k of it is `stepAux_mapS` + `run_embed` |
| Asm.lean header + [SANITY] | 71 | sanity re-derivation of `run_lift` (evidence, could be dropped later) |
| Asm.lean [HOST] (stacks, 5 embeddings, 5 `agree_*`) | 123 | |
| Asm.lean [SEQ] (labels, `hprog`, `hostTM`, 5 `embeds_*`, `seq_run`) | 168 | `seq_run` ≈ 95 |
| Asm.lean [REAL] (`real_run`, `phi_iff`) | 75 | |
| **Assembly so far** | **616** | |

Remaining assembly (D2 precomputation + host prefix composition + polynomial bound in `|w|`): estimate **0.6k–1.0k** (precomputation with `capH` and 12 loads ≈ 0.35k–0.6k,
by comparison with D3Init's precomputation; composition with `real_run` and the `Polynomial` bound ≈ 0.25k–0.4k). Assembly total therefore **≈ 1.2k–1.6k**, inside the
1.0k–2.0k band and narrower. The part done this session went *faster* than the generators (no fix rounds in [SEQ]/[REAL]), because the time lemmas were already in the
"∀ o, ∃ end state, RunLe … ∧ out = w ++ o" shape that `seq_run` consumes.

### Item 6: checks (run this session, output quoted)

* `lake build` after adding D3Init to roots (build_d3init_root.log) and again at the end (build_emb.log): `Build completed successfully (1266 jobs).` Only warnings: the
  three existing `declaration uses 'sorry'` (Challenge.lean:3:8, CookLevin.lean:803:8, SatInP.lean:15:8).
* Emb.lean: `lake env lean Emb.lean` → no output (clean). Asm.lean: toolchain `lean.exe` with `LEAN_PATH=<scratch>;<lake LEAN_PATH>` (scratch `Emb.olean`) → exit 0, no output.
* `#print axioms` on all 50 new declarations (ScratchAsmAx.lean, scratch): 45 ⊆ `[propext, Quot.sound]` (16 use none); `hostTM`, `realProg`, `realB`, `real_run`, `phi_iff`
  → `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.
* Banned-token scan (sorry/admit/axiom/native_decide/decide +native/implemented_by/@[extern]/unsafe/partial/open private/set_option debug./run_cmd/addDecl) on
  Emb.lean, Asm.lean, D3Init.lean, lakefile.toml: no hits.

### Item 7: updated P6 estimate (supersedes the D3Init table)

| Block | Estimate | Basis |
|---|---|---|
| D total | ≈ 7.95k–8.35k (was 7.75k–8.75k) | built ≈ 7.36k (Prog 958, D3Fam 1088, D3OneHot 1005, D3Shift 1375, D3SDef 137, D3Acc 589, D3Init 1599, **Emb 179, Asm 437**); remaining: D2 precomputation + composition + polynomial bound **0.6k–1.0k** |
| A (plumbing) | 250–450, 0.05k done | unchanged (interface now pinned by `real_run`'s preload hypotheses and `phi_iff`'s `hacc`) |
| B | ≈ 0.74k, DONE | |
| C | ≈ 1.7k–1.9k, DONE; slack 0–0.2k | `phi_iff` used none of the slack |
| **Total** | **≈ 10.6k–11.6k lines** (was 10.4k–12.0k) | assembly half measured |

Remaining ≈ 0.8k–1.6k lines (D 0.6k–1.0k + A 0.2k–0.4k + C slack 0–0.2k), roughly 1–3 sessions. This covers **Cook–Levin hardness only**. `sat_in_p`
(part (d), the open problem) is untouched and has no approach. Status: **NOT PROVED**.

### Lakefile

D3Init: applied (approved). **Proposed, NOT applied**: add `"Emb", "Asm"` to `lean_lib` roots (diff in the session report).


# D2 PRECOMPUTATION (Pre.lean): TARGET, stated before any code (2026-10-03)

## Lakefile and housekeeping (done first, this session)

`"Emb", "Asm"` added to `lean_lib` roots (approved in the user's message of 2026-10-03). Stale "not a lakefile root / EXPLORATORY" headers fixed in D3Init,
D3Acc, Asm. ScratchAsmAx.lean moved out of the project folder (to the session scratchpad). `lake build`: `Build completed successfully (1268 jobs).`, only the
three known `sorry` warnings (Challenge.lean:3:8, CookLevin.lean:803:8, SatInP.lean:15:8).

## What the precomputation receives (the D2/A boundary, fixed here)

The reduction machine receives **only the raw input**: a list `s : List (Fin r)` on its input stack `raw` (block A will choose `r = card eb.Γ` and the
equivalence `Fin r ≃ eb.Γ`). Everything else comes from **constants** baked into the program, which block A fixes per NP language:

* `ι : Fin r → M.Γ M.k₀` and `sep : M.Γ M.k₀` (raw symbol ↦ verifier input symbol `inl _`, and the pair separator `inr none`); so
  `x := s.map ι ++ [sep]` (the verifier input `w#`), `|x| = n + 1` with `n = |s|`. The machine only sees the codes `cf = encF E ∘ ι`, `cs = encF E sep`.
* `k` (certificate exponent): `m := n + 1 + n^k`, i.e. `|x ++ y| ≤ m ⟺ |y| ≤ n^k`, **exactly** the NP bound (a larger `m` would admit too-long certificates).
* `c, e` (time constants): `T := (m + c)^e`. Block A must show the verifier's `time.eval` is `≤ T` on every `w#y` with `|y| ≤ n^k` (any `c ≥ 1 + Σ coeffs`,
  `e = natDegree + 1` works; `runI` is stationary after halting, so any upper bound is fine).
* `d := depth M`; `H := capH m T d = m + (T+1)·d + 1`.

## Target theorem (`Pre.full_run`)

A full machine `fprog` on stacks `FK = h (k : HK) | raw | pc (x : PS)` (the host's stacks, the raw input, private scratch counters) with labels
`rd | pre (l : PL) | h (l : HL …)`:

1. `rd` (one label, one step per symbol): a peek-chain over `Fin r` pops the top raw symbol `a`, pushes `cf a` on `h inp` and one unit on `pc N`; on empty
   input it pushes `cs` on `h inp`. Result: `inp = cs :: (s.map cf).reverse = (x.map (encF E)).reverse`, `N = n`.
2. `pre l`: a **pure counter program** on `SK CC` (`CC = s PS | t PT`, 12 scratch + 12 target counters), embedded with `Emb.run_embed`
   (`t` ↦ the 12 host block counters `up/sd/sh/ac .Tn, .Hs`, `ini .Tn/.Xn/.En/.Fn`; `s` ↦ `pc`). It computes `P = n^k` (runtime power loop: `mulS` + drain
   + move, reusing D1/D3OneHot), `Mc = m`, `B = m + c`, `Tc = B^e` (same power loop), `Fx = d·T + d + 1` (`mulS` + constant emit), `Hc = m + Fx`, then loads:
   `Tc → 5 Tn targets`, `Hc → 4 Hs targets`, `iX = n+1`, `iE = n^k`, `iF = Fx`, with one multi-target `xfer` each (new: `xferS`, the multi-target `xfer`
   in the counter view). At `done`: `load false; goto h (ini (pre1 eg))`.
3. `h l`: `mapS` of the host program (`realProg E Ys acc`), embedded with `e = FK.h`, `ι = refl`.

**Statement:** for every `s`, from `⟨some rd, false, fst s⟩` (raw `= s`, all other stacks empty; also proved equal to `initList fullTM s`) the full machine
reaches `⟨some (h fin), v, S⟩` within `fullB n` steps with `S (h out) = encodeCNF (Phi E (s.map ι ++ [sep]) Ys acc (mOf k n) (TOf k c e n))`.
**No hypotheses** beyond the parameters (`|x| ≤ m` becomes a lemma: `n + 1 ≤ n + 1 + n^k`).

**Time:** `fullB n ≤ p.eval n` for an explicit `p : Polynomial ℕ` (built from `X`, `C`, `+`, `*`, `^`; `Polynomial.eval` lemmas).

**Explicitly NOT in this target (block A):** the final cleanup (TM2 `haltList` requires every other stack empty and the state reset; generator and scratch
counters are left non-empty, and the halting label is `h fin`), the `FinTM2` alphabet equivalences, the choice of `r, ι, sep, k, c, e` from the verifier,
and `hacc`.

## Risks flagged in advance

* `TM2` state is `Bool`, so a popped raw symbol cannot be carried in the state: the read loop must branch on it inside one statement (peek-chain).
* `real_run` needs every non-loaded host counter **empty**: comes from `Frame` of the two earlier embedded phases plus the empty start.
* Power loop cost depends on `n^i` at iteration `i`: bounded uniformly by `p₀ (b+1)^j`, so the polynomial is not tight (irrelevant).

## D2 PRECOMPUTATION: RESULTS (same session, checked against the target above)

**Built as stated, no deviation from the target.** Pre.lean, 769 lines, **not a root** (imports `Asm`), checked with `lake env lean Pre.lean`: no output.
Fix rounds: ~10 small ones, none mathematical (two Lean syntax/naming, one `FΓ (h (tgt y))` not reducing to `Unit` for variable `y` (stated as a length fact
instead), one tactic timeout (unification unfolding the huge generator constants `initC`/`genC`/…, fixed by `generalize` plus `with_reducible`)).

### Item 2: the precomputation, and whether multiplication for `capH` needed anything beyond D1

**Nothing new for multiplication itself.** `capH` needs one product: `H − m = (T+1)·d + 1 = d·T + (d+1)` = one `mulS_run` (D1's `mul_run`) plus a constant
emit. What *was* new is all at the counter-view level (Pre.lean [LIB], 177 lines):
* `pow_run`: a runtime power loop `p ← p·b^j` (decrement `kc`; `mulS`; drain `p`; move `q → p`), with bound `powB j p b = j·(p(b+1)^j(3b+5)+5)+1`. Needed for
  `n^k` and `(m+c)^e`, because `k` and `e` are constants of the *language*, while the base is runtime.
* `xferS`: multi-target `xfer` in the counter view (D1's `xfer_run` already supported any `NodupKeys` target list; only the `st`-view wrapper was missing).
  Used for the loads (`Tc` → 5 targets, `Hc` → 4, `P` → `Mc, iE`, …), one pass each.
* `decS_pos`/`decS_zero`: trivial `st`-view wrappers of D1's `decr`.

The counter program (`cprog`, 21 label groups) and `cprog_run` (from `N = n` to all twelve targets) **elaborated in full on the first attempt**, apart from
the final arithmetic (`linarith` after `generalize TOf … = T`). The trick that made it cheap: re-canonicalize the counter function at three checkpoints with
D3OneHot's `bud_st` (`F1`, `F2`, `F3`), so `simp` never sees more than ~6 nested `update`s.

The read loop needed **one** label, not a chain of labels: a single `TM2` statement is a peek-chain over all of `Fin r` (the state is `Bool`, so the popped
symbol cannot be stored; branching inside one statement tree avoids that). One step per input symbol (`read_run`, `|s|+1` steps). On empty input the same
statement pushes the separator code.

### Item 3: composition. **No hypothesis remains, not even `|x| ≤ m`.**

`Pre.full_run E Ys acc ι sep k c e s o`: from `⟨some rd, false, fst s [] 0 o⟩` (raw input `s`, every other stack empty; `initList_full`: this *is*
`initList (fullTM …) s` when `o = []`) the full machine reaches `⟨some (h fin), v, S⟩` within `fullB E Ys k c e |s|` steps with
`S (h out) = encodeCNF (Phi E (s.map ι ++ [sep]) Ys acc (mOf k |s|) (TOf k c e |s|)) ++ o`.
* Hypotheses: **none**. `|x| ≤ m` is discharged inside (`|x| = n+1 ≤ n+1+n^k`). `real_run`'s seven preload hypotheses are discharged from `pre_run`
  (`Agree`/`Frame` of the embedded counter program + the empty start).
* What is still a *parameter* (not a hypothesis): `M`, `E : Enc M`, `Ys`, `acc`, `ι : Fin r → M.Γ M.k₀`, `sep`, `k`, `c`, `e`. Block A instantiates them.
* `fullTM : FinTM2` typechecks (input stack `raw : Fin r`, output stack `h out : Bool`, state `Bool`).
* Structure: `fprog` = read loop (`rd`) + counter program embedded by `Emb.run_embed` (`embC`: `t y ↦` the twelve host block counters, `s x ↦` private `pc x`)
  + host `realProg` embedded by `run_embed` again (`embH = FK.h`, `ι = refl`). Asm.lean was **not edited**; `real_run` is used verbatim.

### Item 4: polynomial time bound. **Proved.**

`fullB n = n + 1 + cB … n + 1 + realB E Ys (mOf k n) (TOf k c e n)` (read + counter program + chain + the five generators).
`fullB_poly : IsPoly (fullB E Ys k c e)` where `IsPoly f := ∃ p : Polynomial ℕ, ∀ n, f n = p.eval n` (closure lemmas `const/id/add/mul/pow`; the proof
unfolds `fullB` and closes structurally after generalizing the five generator constants). `full_time_poly`: **one** `p : Polynomial ℕ` with
`RunLe (fullProg …) (p.eval |s|) …` for every `s`. Equality, not just `≤`: `fullB` *is* a polynomial evaluation.

### Item 5: line counts vs. the 0.6k–1.0k remaining-assembly estimate

| Pre.lean section | Lines |
|---|---|
| header + opens | 35 |
| [LIB] `decS`, `tg`/`xferS`, `PW`/`powS`/`powB`/`pow_run` | 177 |
| [CNT] counters, labels, `cprog`, `mOf`/`TOf`/`F0..F4`/`tv`/`cB`, `cprog_run` | 155 |
| [FULL] `FK`/`FΓ`/`FL`, `tgt`, `embC`/`embH`, `rdT`/`fst`, `rdT_hit`/`rdT_nil`/`read_run` | 167 |
| [COMP] `fprog`, `embeds_*`, `agree_C`, `pre_run` | 76 |
| [REAL] `fullProg`, `fullB`, `full_run`, `fullTM`, `initList_full` | 105 |
| [POLY] `IsPoly` + closure, `fullB_poly`, `full_time_poly` | 54 |
| **Total** | **769** |

Inside the 0.6k–1.0k band (lower-middle). Split vs. the sub-estimates: precomputation 0.35k–0.6k → measured ≈ 0.5k ([LIB]+[CNT]+[FULL]); composition +
polynomial bound 0.25k–0.4k → measured ≈ 0.24k ([COMP]+[REAL]+[POLY]).

### Item 6: checks (run this session, output quoted)

* `lake env lean Pre.lean` → no output (no errors, no warnings).
* `#print axioms` on all **60** Pre declarations (scratch copy `PreAx.lean` = Pre.lean + 60 `#print axioms` lines): 60 results, 0 errors, **0 `sorryAx`**;
  18 `[propext, Classical.choice, Quot.sound]` (incl. `cprog_run`, `pre_run`, `full_run`, `fullB_poly`, `full_time_poly`, `fullTM`, `initList_full`),
  11 `[propext, Quot.sound]`, 16 `[propext]`, 15 none.
* Banned-token scan (sorry/admit/axiom/native_decide/decide +native/implemented_by/@[extern]/unsafe/partial/open private/set_option debug/run_cmd/addDecl,
  plus `macro`/`elab`/`initialize`) on Pre.lean, D3Init.lean, D3Acc.lean, Asm.lean, Emb.lean, lakefile.toml: **0 hits each**. (A first version had a tactic
  `macro "is_poly"`; removed and inlined, since a `macro` command extends the environment and the rules ban environment-editing metaprogramming.)
* `lake build` at the end (build_pre.log): `Build completed successfully (1268 jobs).` Only the three known `sorry` warnings
  (Challenge.lean:3:8, CookLevin.lean:803:8, SatInP.lean:15:8).

### Item 7: what block A must still do to connect `full_run` to `cook_levin` (CookLevin.lean)

`cook_levin : NondeterministicPolynomialTimeComplete (fin_encoding_string Bool) SAT` = `sat_in_np` (done) ∧ for every `β`, `eb : FinEncoding β`, `L'` with
`InNondeterministicPolynomialTime eb L'`, a `PolynomialTimeReducible eb (fin_encoding_string Bool) L' SAT`. Given the NP data `(Γ₁, R, kk, verifier)`:

1. **Unpack the verifier**: its `FinTM2` `Mv`, the equivalence `Mv.Γ Mv.k₀ ≃ Sum eb.Γ (Option Γ₁)` (pair encoding), the output equivalence to `Bool`, the
   time polynomial `tp`, and the decider `fv` with `R a y ↔ fv (a, y) = true`. Set `E := Enc.ofFinTM2 Mv`.
2. **Instantiate the parameters**: `r := card eb.Γ` with `Fin r ≃ eb.Γ` (`Fintype.equivFin`); `ι i := inv (inl (eqv i))`, `sep := inv (inr none)`;
   `Ys :=` the list of `inv (inr (some γ))` over all `γ : Γ₁`; `acc :=` the output symbol for `true`; `k := kk`; `c, e` with
   `tp.eval ℓ ≤ (ℓ + c)^e` for all `ℓ` (e.g. `c = 1 + Σ coeffs`, `e = natDegree + 1`; plus `tp.eval` monotone, so `≤ T` for every `ℓ ≤ m`).
3. **Halting cleanup** (the only new machine work): the full machine stops at `h fin` with non-empty generator, scratch and `inp` stacks. `haltList`
   needs label `none`, state `false`, every stack except `h out` empty. Replace `h fin` by a drain of every other stack (finitely many; `xfer k []` drains
   any alphabet), then `load false; halt`. Its time needs a **generic stack-growth lemma** (each step pushes ≤ a constant per statement, so every stack has
   length ≤ const · steps); this lemma does not exist yet. The `Embeds` halt exception (`realProg .fin = .halt`) means `full_run`'s proof is unchanged
   if `fprog`'s `.h .fin` case is redirected.
4. **`TM2OutputsInTime` from `RunLe`**: convert `Run` (iterate of `TM2.step`) to `EvalsToInTime` with the final `some (haltList …)`, and give the
   `TM2ComputableInPolyTime` structure: `inputAlphabet := Fin r ≃ eb.Γ`, `outputAlphabet := Equiv.refl Bool`, `time :=` the polynomial from
   `full_time_poly` plus the cleanup polynomial (`IsPoly` closure).
5. **Correctness** `L' a ↔ SAT (f a)` with `f a := encodeCNF (Phi …)`: `phi_iff` + (i) `y ∈ Ys*` ⇔ `y = inv ∘ inr ∘ some` of some `y' : List Γ₁`, and
   `s.map ι ++ [sep] ++ y` = the verifier's encoded `(a, y')`; (ii) `|x ++ y| ≤ m ⇔ |y'| ≤ |eb.encode a|^kk` (already exact by the choice of `m`);
   (iii) `Accepts Mv (runI …) T acc ⇔ R a y'` via `Sit.runI_haltList` + `accepts_haltList` (exist) and `T ≥ tp.eval |w#y|`; (iv) `SAT` is defined on
   `List Bool` via `decodeCNF`, so check that `SAT (encodeCNF F) ↔ ∃ a, cnfSat F a` for the dense format (`decodeCNF_encodeCNF` exists).
6. **`hacc`** (`∃ i, E.dec Mv.k₁ i = acc`): holds whenever **some** pair is accepted (an output symbol on the stack lies in `symSet`, by `Enc.run_good`). If
   no pair is accepted, `L' = ∅`: case-split and reduce by a constant machine emitting a fixed unsatisfiable formula (or show `Phi` unsatisfiable directly).
7. **Not needed**: no composition of reductions (Mathlib's missing `comp` is already `PvsNP.comp`); `D3SDef` stays reached only through `sdef_time`.

### Lakefile

**Proposed, NOT applied**: add `"Pre"` to `lean_lib` roots (diff in the session report).

### Updated P6 estimate (supersedes the 2026-10-02 table)

| Block | Estimate | Basis |
|---|---|---|
| D total | ≈ 8.13k, **DONE** except the halting cleanup | built: Prog 958, D3Fam 1088, D3OneHot 1005, D3Shift 1375, D3SDef 137, D3Acc 589, D3Init 1599, Emb 179, Asm 437, **Pre 769** |
| A (plumbing) | 0.45k–0.85k remaining (was 250–450) | items 1–6 above; raised because the halting cleanup + a generic stack-growth lemma (0.15k–0.3k) and the `hacc` case split (0.05k–0.1k) are now explicit A work |
| B | ≈ 0.74k, DONE | |
| C | ≈ 1.7k–1.9k, DONE; slack 0–0.2k | |
| **Total** | **≈ 11.0k–11.8k lines** (was 10.6k–11.6k) | D measured; only A left |

Remaining ≈ 0.45k–1.05k lines (A 0.45k–0.85k + C slack 0–0.2k), roughly 1–2 sessions. This covers **Cook–Levin hardness only**. `sat_in_p` (part (d), the
open problem) is untouched and has no approach. Status: **NOT PROVED**.


# BLOCK A, ITEMS 3–4: HALTING CLEANUP AND PACKAGING (Pkg.lean): TARGET, stated before any code (2026-10-04)

## Lakefile and housekeeping (done first, this session)

`"Pre"` added to `lean_lib` roots (approved in the user's message of 2026-10-04). `lake build` (build_pre_root.log):
`✔ [1268/1269] Built Pre (27s)` / `Build completed successfully (1269 jobs).`; only the three known `sorry` warnings
(Challenge.lean:3:8, CookLevin.lean:803:8, SatInP.lean:15:8).

## The gap

`Pre.full_run` ends at `⟨some (h fin), v, S⟩` with `S (h out) = encodeCNF (Phi …)`, but `TM2OutputsInTime` needs the run to end in exactly
`haltList tm out = ⟨none, initialState = false, fun k => if k = k₁ then out else []⟩`: label `none`, state `false`, **every** other stack empty.
After `full_run`, `raw` is empty, but `inp`, the generators' private counter blocks and the scratch counters `pc B`, `pc Dd` are not.

## Target 1: generic stack growth (reuse, not new)

`Sit.stepI_height`/`Sit.runI_height` are **already generic** (any `M : FinTM2`, growth `≤ depth M` per step of the idle-extended step `stepI`).
New, generic over `M : FinTM2`:
* `run_runI : Run M.m n c d → runI M c n = d` (a real run is the idle-extended run);
* `run_height : Run M.m n c d → (d.stk k).length ≤ (c.stk k).length + n · depth M`.
Applied to `fullTM` (constant `D := depth fullTM`, independent of the input), after `full_run`'s `n ≤ fullB |s|` steps every stack has length
`≤ |s| + fullB |s| · D`.

## Target 2: generic drain phase

Generic in `K, Γ, Λ, σ` with `[Flag σ]`:
* `xfer_drain : M self = xfer k [] self next → S k = l → Run M (|l| + 1) ⟨some self, v, S⟩ ⟨some next, tag false, update S k []⟩`
  (any contents, not only counters; D1's `xfer_run` needs `S k = cnt u n`);
* `drainS ks lab i` = `xfer ks[i] [] (lab i) (lab (i+1))` for `i < |ks|`, else `load (tag false); halt`;
* `drain_run`: `ks.Nodup`, `M (lab i) = drainS ks lab i` for `i ≤ |ks|` ⟹
  `Run M (Σ_{k∈ks} (|S k| + 1) + 1) ⟨some (lab 0), v, S⟩ ⟨none, tag false, fun k => if k ∈ ks then [] else S k⟩`.

## Target 3: the composed machine

Labels `DL Λ n = f (l : Λ) | dr (i : Fin (n+1))`; drain list `dks = (univ.erase (h out)).toList` (every stack except the output).
`gprog`: `f l ↦` `goto (dr 0)` if `l = h fin`, else `fullProg l` relabelled by `mapS` with the identity stack embedding; `dr i ↦ drainS dks …`.
`full_run` transfers by `Emb.runLe_embed` (halt exception: `fullProg (h fin) = halt`). `gTM : FinTM2` (input `raw`, output `h out`).
**Statement (`g_run`)**: for every `s`, `Run gTM.m n (initList gTM s) (haltList gTM (encodeCNF (Phi E (s.map ι ++ [sep]) Ys acc (mOf k |s|) (TOf k c e |s|))))`
with `n ≤ gB |s| := fullB |s| + 1 + |dks| · (|s| + fullB |s| · D + 1) + 1`. No hypotheses.

## Target 4: packaging

`TM2OutputsInTime gTM s (some phi) (p.eval |s|)` for one polynomial `p` (`IsPoly gB` from `fullB_poly` + closure), and, for any encoding
`ea : α → List αΓ` and `eqv : Fin r ≃ αΓ`, a structure `TM2ComputableInPolyTime ea (fin_encoding_string Bool).encode fR` with
`fR a = encodeCNF (Phi E (((ea a).map eqv.symm).map ι ++ [sep]) …)`, `inputAlphabet = eqv`, `outputAlphabet = Equiv.refl Bool`.
Parameters (`M, E, Ys, acc, ι, sep, k, c, e, eqv`) stay parameters: choosing them from the verifier is item 2 (next session).
Not this session: items 1, 2, 5, 6; no edit to `cook_levin`.

## Risks flagged in advance
* `haltList`/`initList` use `dite` + `cast` on `k = k₁`; equality per stack by case split (as in `initList_full`).
* `TM2ComputableInPolyTime` is data (`EvalsTo.steps : ℕ`); built from the `RunLe` existential with `Classical.choose` (allowed axiom).

## HALTING CLEANUP + PACKAGING: RESULTS (same session, checked against the target above)

**Built as stated, no deviation from the target.** Pkg.lean, 365 lines, **not a root** (imports `Pre`), checked with `lake env lean Pkg.lean`: no output.
Fix rounds: 5, none mathematical (`Run 0` unfolding; `pushAll []` not unfolded by `simp`; a `▸` needing a type ascription; dependent-type mismatch
between `gTM.Γ gTM.k₁` and `FΓ … (h out)` when rewriting under `haltList` (fixed by turning the drained stacks into an `if q = h out` form *before*
touching `haltList`, then `rcases` + `rfl` per constructor); `omega` seeing `s.length` at two different list types (fixed by a type-ascribed `have`)).

### Item 2: the stack-growth lemma. **Overlaps fully with `stepI_height`; reused, not reproved.**

`Sit.stepI_height` and `Sit.runI_height` were already generic (any `M : FinTM2`, growth `≤ depth M` per idle-extended step). The only new
piece is the bridge from `Prog.Run` (iterate of `TM2.step`) to `Sit.runI`: `run_runI` (16 lines) and `run_height` (5 lines):
`Run M.m n c d → (d.stk k).length ≤ (c.stk k).length + n · depth M`. Applied to `fullTM` (not to `gTM`), since the heights needed are those at
the end of `full_run`; `D = depth fullTM` is a constant of the language (it does not depend on the input).

### Item 3: the drain and the composed machine. **No hypotheses.**

* `xfer_drain`: D1's `xfer k []` empties a stack of **any** contents (D1's `xfer_run` needs a counter `cnt u n`) in `|l| + 1` steps.
* `drain_run` (generic in `K, Γ, Λ, σ`, `[Flag σ]`): stages `lab 0 … lab |ks|`, each empties `ks[i]`, the last does `load (tag false); halt`.
  Ends in `⟨none, tag false, fun k => if k ∈ ks then [] else S k⟩` after `drainB ks S = Σ (|S k| + 1) + 1` steps.
* `gprog P fin` (generic in the inner program `P` and its halting label): labels `DL Λ n = f l | dr (i : Fin (n+1))`; `f fin ↦ goto (dr 0)`,
  other `f l ↦ mapS (idE) DL.f (P l)` (identity stack embedding = relabelling), `dr i ↦ drainS dks …`; `dks = (univ.erase (h out)).toList`.
  `g_run_gen`: a `RunLe P B` run ending at `fin` becomes a `RunLe (gprog P fin) (B + 1 + drainB dks T)` run ending at the drained configuration.
  `Pre.full_run` transferred via `Emb.runLe_embed` using the halt exception (`fullProg (h fin) = halt` by `rfl`). **Pre.lean not edited.**
* `gTM : FinTM2` (input `raw`, output `h out`, state `Bool`, initial `false`). `initList_g`, `haltList_g` (exact `TM2.Cfg` equalities).
* **`g_run`**: `RunLe gTM.m (gB |s|) (initList gTM s) (haltList gTM (phiOf s))`, `phiOf s = encodeCNF (Phi E (s.map ι ++ [sep]) Ys acc (mOf k |s|) (TOf k c e |s|))`,
  `gB n = fullB n + 1 + (|dks| · (n + fullB n · D + 1) + 1)`. Hypotheses: none.

### Item 4: `TM2OutputsInTime` and `TM2ComputableInPolyTime`. **Built.**

* `outputsOfRunLe`: `RunLe tm.m B (initList tm l) (haltList tm l') → TM2OutputsInTime tm l (some l') B` (data, via `Classical.choose`; `Run` *is*
  `(flip bind tm.step)^[n] (some c) = some d`, so `evals_in_steps` is the run itself).
* `gB_poly : IsPoly gB` (closure from `fullB_poly`, after generalizing `D` and `|dks|`); `g_outputs`: **one** `p` with `TM2OutputsInTime` for every `s`.
* **`gComp ea eqv … : TM2ComputableInPolyTime ea (fin_encoding_string Bool).encode (fR …)`**, `fR a = phiOf ((ea a).map eqv.invFun)`,
  `inputAlphabet = eqv : Fin r ≃ αΓ`, `outputAlphabet = Equiv.refl Bool`, `time = choose gB_poly`. The output side needed `List.map id` ↦ id
  (`outputsOfRunLe'`, an equation on the output); the length side `List.length_map`.
* Fit check (scratch `example`): for `eb : FinEncoding β`, `⟨_, gComp E eb.encode eqv …, trivial⟩ : ∃ f (_ : TM2ComputableInPolyTime eb.encode
  (fin_encoding_string Bool).encode f), True` elaborates, i.e. exactly the shape `PolynomialTimeReducible eb (fin_encoding_string Bool) L' SAT` asks for.

### Item 5: line counts vs. the block A estimate

| Pkg.lean section | Lines |
|---|---|
| header + opens | 28 |
| [GROW] `run_runI`, `run_height` | 36 |
| [DRAIN] `xfer_drain`, `drainS`, `drainB`, `drain_run` | 75 |
| [GLUE] `DL`, `dlab`, `idE`, `dks`, `drained`, `gprog`, `embeds_g`, `g_run_gen`, `drainB_le` | 76 |
| [REAL] `fullProg_fin`, `gTM`, `phiOf`, `gB`, `initList_g`, `haltList_g`, `g_run` | 85 |
| [PKG] `outputsOfRunLe(')`, `gB_poly`, `g_outputs`, `fR`, `gComp` | 65 |
| **Total** | **365** |

Against the 2026-10-03 sub-estimate for these items (cleanup + stack growth 0.15k–0.3k, plus packaging inside the remaining A band): cleanup + growth
measured ≈ 0.27k ([GROW]+[DRAIN]+[GLUE]+[REAL] minus header), packaging ≈ 0.07k. Block A so far: 0.365k of the 0.45k–0.85k band.

### Item 6: checks (run this session, output quoted)

* `lake env lean Pkg.lean` → no output.
* `#print axioms` on all **30** Pkg declarations (scratch `PkgAx.lean` = Pkg.lean + 30 `#print axioms` lines + the fit `example`): 30 results, no errors,
  **0 `sorryAx`**: `22 [propext, Classical.choice, Quot.sound]` (incl. `g_run`, `g_outputs`, `gComp`, `drain_run`, `run_height`, `gTM`),
  `4 [propext, Quot.sound]` (`run_runI`, `dlab`, `phiOf`, `fR`), `2 [propext]` (`drainS`, `drainB`), `2` none (`DL`, `idE`).
* Banned-token scan (sorry/admit/axiom/native_decide/decide +native/implemented_by/@[extern]/unsafe/partial/open private/set_option debug/run_cmd/addDecl,
  plus `macro`/`elab`/`initialize`) on Pkg.lean, Pre.lean, lakefile.toml: **0 hits each**.
* `lake build` at the end (build_pkg.log): `Build completed successfully (1269 jobs).`, only the three known `sorry` warnings
  (Challenge.lean:3:8, CookLevin.lean:803:8, SatInP.lean:15:8).

### Item 7: what remains for `cook_levin` (block A items 1, 2, 5, 6)

Fixed by this session: `cook_levin`'s reduction is `⟨fR E eb.encode eqv Ys acc ι sep kk c e, gComp …, correctness⟩`.
1. **Unpack the verifier** (item 1): from `InNondeterministicPolynomialTime eb L'` get `Γ₁`, `R`, `kk`, and from `PolynomialTimeCheckingRelation` the
   `InPolynomialTime (pair_encoding eb (fin_encoding_string Γ₁))` data: `fv`, its `TM2ComputableInPolyTime` (machine `Mv`, alphabet equivalences
   `Mv.Γ Mv.k₀ ≃ Sum eb.Γ (Option Γ₁)`, `Mv.Γ Mv.k₁ ≃ Bool`, polynomial `tp`). `E := Enc.ofFinTM2 Mv` (exists, Sit.lean:486).
2. **Parameters** (item 2): `r := card eb.Γ`, `eqv := (Fintype.equivFin eb.Γ).symm`; `ι i := inv (inl (eqv i))`, `sep := inv (inr none)`;
   `Ys := univ.toList.map (inv ∘ inr ∘ some)`; `acc := outInv true`; `k := kk`; `c, e` with `tp.eval ℓ ≤ (ℓ + c)^e` (monotone) for all `ℓ`.
3. **Correctness** (item 5): `L' a ↔ SAT (fR a)`. `SAT w = ∃ a, cnfSat (decodeCNF w) a` and `decodeCNF_encodeCNF` give `SAT (encodeCNF F) ↔ ∃ a, cnfSat F a`;
   then `Asm.phi_iff`; then (i) `Ys*` ↔ certificates `y' : List Γ₁` and `x ++ y` = the verifier's pair encoding of `(a, y')` (with
   `(ea a).map eqv.invFun` mapped by `ι` = `inl`-tagged input); (ii) `|x ++ y| ≤ m ↔ |y'| ≤ |eb.encode a|^kk` (exact by `mOf`); (iii)
   `Accepts Mv (runI …) T acc ↔ fv (a, y') = true` via `runI_haltList`/`accepts_haltList` + `T ≥ tp.eval |w#y|` + `run_runI` (this session's bridge).
4. **`hacc`** (item 6): `∃ i, E.dec Mv.k₁ i = acc`; holds if some pair is accepted; otherwise `L' = ∅` and the reduction can be any machine with
   unsatisfiable output (case split; the `L' = ∅` branch can reuse `gComp` only if `Phi` is shown unsatisfiable, or use a constant machine).

### Lakefile

**Proposed, NOT applied**: add `"Pkg"` to `lean_lib` roots (diff in the session report).

### Updated P6 estimate (supersedes the 2026-10-03 table)

| Block | Estimate | Basis |
|---|---|---|
| D total | ≈ 8.13k, **DONE** | Prog 958, D3Fam 1088, D3OneHot 1005, D3Shift 1375, D3SDef 137, D3Acc 589, D3Init 1599, Emb 179, Asm 437, Pre 769 |
| A (plumbing) | 0.365k done (Pkg) + **0.25k–0.55k remaining** | items 1+2 0.1k–0.2k, item 5 0.12k–0.3k, item 6 0.03k–0.05k |
| B | ≈ 0.74k, DONE | |
| C | ≈ 1.7k–1.9k, DONE; slack 0–0.2k | |
| **Total** | **≈ 11.2k–11.8k lines** (was 11.0k–11.8k) | only A items 1, 2, 5, 6 left |

Remaining ≈ 0.25k–0.75k lines (A 0.25k–0.55k + C slack 0–0.2k), one session if item 5 has no surprise. This covers **Cook–Levin hardness only**.
`sat_in_p` (part (d), the open problem) is untouched and has no approach. Status: **NOT PROVED**.

## CLOSE cook_levin (2026-10-05): statement recorded BEFORE any proof work

Verbatim copy of CookLevin.lean line 803 at session start (sha256 of the line, no newline: e736e5ad76e2e4efb0017dee202b0d7115b00326761431c112142833cdc847eb):

    theorem cook_levin : NondeterministicPolynomialTimeComplete (fin_encoding_string Bool) SAT := sorry

The proof must establish exactly this declaration (name `PvsNP.cook_levin`, same type); no hypotheses may be added.

## CLOSE cook_levin: RESULTS (2026-10-05)

**`PvsNP.cook_levin` is proved.** `#print axioms PvsNP.cook_levin` → `[propext, Classical.choice, Quot.sound]`.
Overall status is still **NOT PROVED**: `sat_in_p` (part (d), the open problem) is untouched and is now the only `sorry` that `p_eq_np` depends on.

### Location change (forced, statement unchanged)
D3Fam imports CookLevin, so the whole reduction chain (D3Fam → … → Pkg) sits above CookLevin.lean and the proof cannot live there (import cycle).
The `sorry` declaration was removed from CookLevin.lean and `theorem cook_levin` is stated and proved at the end of Pkg.lean (already a root, so no further lakefile change), in `namespace PvsNP` with `open Millennium` as before. Solution.lean gained `import Pkg`; its theorem text is unchanged.
Evidence that the statement is unchanged:
* source header `theorem cook_levin : NondeterministicPolynomialTimeComplete (fin_encoding_string Bool) SAT`: sha256 `d8dc8def411b7de8a7e8d83ae13d8dc02451b34378b3c701b2d8c1b0ef8ce2f8` in the session-start CookLevin.lean backup and in Pkg.lean;
* elaborated type with `set_option pp.all true` (`#check @PvsNP.cook_levin`), before (importing CookLevin) and after (importing Pkg): byte-identical, sha256 `3f65cab8…77dd85` both:
  `PvsNP.cook_levin : @Millennium.NondeterministicPolynomialTimeComplete (List.{0} Bool) (@Millennium.fin_encoding_string Bool Bool.fintype) PvsNP.SAT`.

### Item 5 (correctness): no gap
`v_correct` needed only `phi_iff`, `runI_haltList`, `accepts_haltList`, `decodeCNF_encodeCNF`, plus two small new lemmas: `pull` (a list all of whose elements lie in `L.map f` is `l0.map f`, which recovers the certificate) and `eval_le_pow`/`eval_mono'` (time bound).
`run_runI` was not needed. Pair encoding: `v_input` shows the verifier's input on `(a, y)` is `(w.map ι) ++ [sep] ++ y.map vY` (one `erw` for the `pair_symbol`/`Sum` defeq). Accepting-run correspondence: `runI` at row `T` equals `haltList [oa⁻¹ (fv (a,y))]` whenever `time(|w|+1+|y|) ≤ T`, so `Accepts` ⇔ `fv (a,y) = true` by injectivity of `outputAlphabet`.
Length cap `m = n+1+n^k` matches `|y| ≤ n^k` exactly in both directions.

### Item 6: replaced, no case split
`hacc` fails for `Enc.ofFinTM2` only because the accept symbol might never be pushed. `encX` is `Enc.ofFinTM2` with `acc` added to the output stack's effective alphabet (`symSetX = symSet ∪ {acc}`). Every `Enc` field still holds, so `five_iff`/`phi_iff` apply with `hacc` proved outright (`encX_acc`). No constant-output machine and no empty-language split were needed.

### Items 1–2
`r = |eb.Γ|`, `eqv = (equivFin eb.Γ)⁻¹`, `ι i = ia⁻¹ (inl (eqv i))`, `sep = ia⁻¹ (inr none)`, `Ys` = `ia⁻¹ (inr (some g))` over all `g : Γ₁`, `acc = oa⁻¹ true`, `k` = the NP exponent, `(c, e)` from `eval_le_pow` on the verifier's time polynomial.

### Line counts
* Pkg.lean 365 → 603 (+238; the new section is 237 lines including docs and blank lines). CookLevin.lean 805 → 803. Solution.lean +1 line (import).
* Estimate was 0.25k–0.55k for A items 1, 2, 5, 6; actual ≈ 0.24k, just under the low end. Item 6 cost ≈ 50 lines (`encX`) instead of a machine.
* Cook–Levin hardness development, same basis as the P6 table (Prog, D3Fam, D3OneHot, D3Shift, D3SDef, Sit, D3Acc, D3Init, Emb, Asm, Pre, Pkg): **11,577 lines** (estimate 11.2k–11.8k). With CookLevin.lean (SAT definition + `sat_in_np`, 803) and without the unused D3SDef (137): 12,243 lines in the build chain.

### Checks (run 2026-10-05)
* `lake build`: `Build completed successfully (1270 jobs)`, only warnings `Challenge.lean:3:8` and `SatInP.lean:15:8` (`declaration uses 'sorry'`).
* `#print axioms p_eq_np` → `[propext, sorryAx, Classical.choice, Quot.sound]`; closure scan: only direct `sorryAx` user is `PvsNP.sat_in_p`. `comp`, `sat_in_np`, `cook_levin` and the Millennium bridge theorem each → `[propext, Classical.choice, Quot.sound]`.
* Banned-token scan of Solution.lean and all 14 project files it imports: only hit is `SatInP.lean:15` (`sat_in_p … := sorry`).
* lean4checker: not run (owed before any READY FOR CHECK; not applicable while `sat_in_p` is open).

---

## PRIOR WORK (comparison session, 2026-10-05, read-only except this section)

Sources were read directly where possible: Complexitylib was cloned to the session scratchpad (branch `dev`, HEAD `1c876ef`, 2026-10-04) and its source grepped. Mathlib master and PRs were checked through raw.githubusercontent and the GitHub search API. Other entries come from READMEs and abstracts only and are marked as such.

### Existing Cook-Levin formalizations (all three-axiom, none `sorry`)

| Development | System | Machine model | Statement target | Notes |
|---|---|---|---|---|
| Gäher–Kunze, ITP 2021 | Coq | call-by-value λ-calculus L | own definitions | first mechanised Cook-Levin (paper abstract) |
| Balbach, AFP `Cook_Levin` (2023-01-08) | Isabelle/HOL | deterministic multi-tape TMs (Arora–Barak), two-tape oblivious TM for verifiers | own P/NP/SAT | AFP abstract |
| **Complexitylib** (Schlesinger), Cook-Levin closed 2026-07-03 | Lean v4.35.0-rc3, Mathlib `728a93ee`, plus CSLib | own Arora–Barak k-work-tape TM/NTM over `Γ = {0,1,□,▷}` (`Complexity.TM`/`NTM`); reduced to single-tape before the tableau | own: `Language := Set (List Bool)`, `P = ⋃k DTIME(n^k)`, `NP = ⋃k NTIME(n^k)` (NTM-based), `≤ₚ` via own `FP`, `SAT.language = {φ.encode \| φ satisfiable}` | headline `Complexity.SAT.NPComplete_language : NPComplete language`; CI `AxiomGuard` enforces `[propext, Classical.choice, Quot.sound]`; `native_decide` only in `Validation` example files. SAT/ ≈ 28.6k lines, Cook-Levin core (`CookLevin.lean` + `CookLevin/`) ≈ 8.6k, plus `VerifierTM` 5.3k and `Internal/GuessVerify` 4.4k; whole library ≈ 735k lines. Also has `language_mem_P_iff_P_eq_NP`, 3SAT, Savitch, PCP, etc. |
| RBarish-UTokyo/NPCompleteness-Lean4 | Lean v4.35.0-rc2, **core only, no Mathlib** | single-tape TM, 4-symbol alphabet | own statement in a Palomar/Comparator Challenge | README: ≈41k lines, SAT/3SAT/planar 3SAT etc. NP-complete |
| DominicBreuker/cook-levin-lean | Lean + Mathlib | single-tape TM, proved through a custom register language and compiler | own | README only |
| Reed, Zenodo 18993257 (2026-02) | Lean 4 | deterministic TM → CNF | encoding correctness; full NP-hardness / poly-time not evident from the abstract | abstract only |
| solresol, project-intentions #52 (2026-10-03) | Lean + Mathlib | multistack TM interfaces | Cook-Levin listed as a *pending* goal | intention only |

**None of these targets `Millennium.ClayPVersusNP`, Mathlib's `Turing.TM2ComputableInPolyTime`, or the `FinEncoding`-based `InNondeterministicPolynomialTime` / `PolynomialTimeReducible` of LeanMillenniumPrizeProblems.** A grep of Complexitylib for `TM2Computable`, `Turing.TM2`, `ClayPVersusNP`, `Millennium` and `InNondeterministicPolynomialTime` returned nothing. A web search found no other Cook-Levin proof stated against the Millennium-repo definitions.

### Mathlib `proof_wanted TM2ComputableInPolyTime.comp`

* Still open on master, now in `Wanted/Computability/TuringMachine/Computable.lean:20` (the signature is unchanged from our pinned copy at `Mathlib/Computability/TuringMachine/Computable.lean:284`).
* **A pending PR exists:** mathlib4 #44441 by `vincentqb`, opened 2026-10-02, "prove `TM2ComputableInPolyTime.comp` (`proof_wanted`)". It is labelled `LLM-generated`, `new-contributor`, `blocked-by-other-PR` and has no reviewer yet. It depends on #44440 (same author, same date: TM2 output-length bound, `TM2ComputableInPolyTime.length_le`). Original `proof_wanted` came from #7172 (2023).
* Our `PvsNP.tm2ComputableInPolyTime_comp` (Comp.lean, 2026-09-25) is independent and earlier, but unpublished. If #44441 merges, our Comp result duplicates upstream Mathlib.

### Blunt assessment

**Not new:**
* The Cook-Levin theorem as mathematics, and as a sorry-free three-axiom machine-checked proof. It exists in Coq (2021), Isabelle (2023) and at least two complete Lean 4 developments: Complexitylib (2026-07, Mathlib-based, far larger and broader) and NPCompleteness-Lean4. Complexitylib substantially duplicates the *theorem*. Its tableau method (one-hot state/cell/head variables, frame and transition clauses, `Represents` induction) is the same textbook construction as our D3/Sit families.
* TM2 polytime composition: proved independently by pending mathlib4 #44441.
* SAT ∈ NP: in every development above.
* Anything toward (d) `sat_in_p`. Nothing here moves P vs NP. NP-completeness of SAT under the Clay definitions only re-expresses `p_eq_np` as `sat_in_p` (Millennium's `nondeterministic_polynomial_time_complete_in_polynomial_time` already did this, modulo comp and an NP-complete language).

**Genuinely new, as far as this search found (modest, mainly engineering):**
1. Cook-Levin stated and proved **against the LeanMillenniumPrizeProblems definitions**: `NondeterministicPolynomialTimeComplete (fin_encoding_string Bool) SAT`, over Mathlib's `FinTM2` / `TM2ComputableInPolyTime` and `FinEncoding`, with hardness for NP languages under *any* `FinEncoding`. This discharges two of the three hypotheses of the Clay reduction, `comp` and `cook_levin`, with no axioms beyond the three standard ones. Prior Lean developments use their own TM models and cannot be plugged into `ClayPVersusNP` without a model-equivalence proof, which nobody has done.
2. A reduction machine built **directly in Mathlib's multi-stack TM2 model** (no tapes; stack-height cap `capH`, situation tables for an arbitrary `FinTM2`, `step_agree` with no hypotheses), plus the generic `Emb.run_embed` stack/label embedding and the `Prog` step-counting library for TM2. Nobody else has a Cook-Levin over TM2. This is new infrastructure but has not been reviewed or published.
3. Comp. It was independent and earlier (2026-09-25 vs 2026-10-02), but the novelty is weak: a competing PR is already open upstream, and ours is unpublished.

**Caveats for any writeup:** `PvsNP.SAT` is this project's own dense-CNF encoding over `List Bool`. "SAT" in our `cook_levin` means that language, so a writeup must state the encoding (DEFINITIONS.md). Size is about 13.0k lines across the 14 root files `Solution` imports, versus about 8.6k for Complexitylib's Cook-Levin core (which uses a tape model with its own prior infrastructure). Status of the project is unchanged: **NOT PROVED**.
