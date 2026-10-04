import Sit
import Comp

namespace PvsNP.Sit

open Turing Function

theorem exM_pushBound : PvsNP.Comp.pushBound exM = 4 := by
  unfold PvsNP.Comp.pushBound
  rfl

/-- P2's cap `H = m + c*T + d + 1` (c = pushBound, d = depth) does NOT satisfy
`l + (T+1)*d <= H` for exM once `T >= 2` (with l = m, the largest admissible input bound). -/
theorem exM_H_fails_c1 (m : ℕ) : ¬ (m + (2 + 1) * depth exM ≤
    m + PvsNP.Comp.pushBound exM * 2 + depth exM + 1) := by
  rw [exM_pushBound, ex_depth]; omega

/-- ... and `H >= 2d` fails for `m = 1`, `T = 0`. -/
theorem exM_H_fails_c2 : ¬ (2 * depth exM ≤ 1 + PvsNP.Comp.pushBound exM * 0 + depth exM + 1) := by
  rw [exM_pushBound, ex_depth]; omega

/-! Corrected cap (fix A, 2026-09-30 sixth session): `capH m T d = m + (T+1)*d + 1`. -/

/-- Constraint 1 now holds for exM for every `m, T` (the case that failed above). -/
theorem exM_capH_c1 (m T : ℕ) : m + (T + 1) * depth exM ≤ capH m T (depth exM) :=
  capH_c1 le_rfl

/-- Constraint 2 still fails at `T = 0` for exM with `m = 1` (`12 ≤ 8` is false) ... -/
theorem exM_capH_c2_fails_T0 : ¬ (2 * depth exM ≤ capH 1 0 (depth exM)) := by
  rw [ex_depth]; decide

/-- ... and holds for every `T ≥ 1`. -/
theorem exM_capH_c2 (m T : ℕ) (hT : 1 ≤ T) : 2 * depth exM ≤ capH m T (depth exM) := capH_c2 hT

#print axioms capH_height
#print axioms depth_le_capH
#print axioms capH_c1
#print axioms capH_c2
#print axioms runI_height
#print axioms initList_height
#print axioms region_cover
#print axioms Enc.cells_step_run
#print axioms Enc.row_step_run
#print axioms Enc.row_step_capH
#print axioms exM_capH_c1
#print axioms exM_capH_c2_fails_T0
#print axioms exM_capH_c2
#print axioms exM_H_fails_c1

end PvsNP.Sit
