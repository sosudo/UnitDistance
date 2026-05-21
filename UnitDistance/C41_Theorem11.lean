import Mathlib
import UnitDistance.C01_UnitDistanceFunctions
import UnitDistance.C31_Theorem23
import UnitDistance.C32_Prop38

set_option linter.style.longLine false

namespace UnitDistance

open Real

/-- Theorem 1.1 (Main Result): There exists an absolute constant δ > 0 and
    infinitely many positive integers n such that ν(n) ≥ n^{1+δ}.
    This disproves the Erdős unit-distance conjecture. -/
theorem theorem11_mainResult :
    ∃ δ : ℝ, δ > 0 ∧
      ∃ nseq : ℕ → ℕ,
        (∀ j, nseq j < nseq (j+1)) ∧
        (∀ j, (maxUnitDistancePairs (nseq j) : ℝ) ≥ (nseq j : ℝ) ^ (1 + δ)) := by
  sorry

end UnitDistance
