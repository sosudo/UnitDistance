import Mathlib

set_option linter.style.longLine false

namespace UnitDistance

/-- ν(P): the number of unordered unit-distance pairs in a finite planar set P ⊆ ℝ². -/
noncomputable def unitDistancePairs (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  ((P ×ˢ P).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1)).card / 2

/-- ν(n): the maximum number of unit-distance pairs over all n-point subsets of ℝ². -/
noncomputable def maxUnitDistancePairs (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n ∧ unitDistancePairs P = k}

end UnitDistance
