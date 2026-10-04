import CookLevin

/-!
# SAT ∈ P (PLACEHOLDER — the open problem)

This is part (d) of the plan: the unresolved core of P vs NP. It stays a single named lemma so
the gap is always explicit.
-/

namespace PvsNP

open Millennium

/-- SAT is decidable in polynomial time. **Open problem.** -/
theorem sat_in_p : InPolynomialTime (fin_encoding_string Bool) SAT := sorry

end PvsNP
