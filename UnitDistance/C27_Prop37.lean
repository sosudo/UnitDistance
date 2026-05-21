import Mathlib
import UnitDistance.C08_Discriminants
import UnitDistance.C16_MinkowskiClassNumber

set_option linter.style.longLine false

namespace UnitDistance.NumberTheory

open NumberField

/-- Proposition 3.7 (Class number bound, citing A.13):
    There exists an absolute constant C_class : ℝ with C_class > 0 such that
    for every number field K:
    h(K) ≤ max{2, rd(K)}^{C_class · [K:ℚ]},
    where h(K) = |ClassGroup(𝓞 K)| and rd(K) = |D_K|^{1/[K:ℚ]}.
    This restates the Minkowski class number bound axiom from A.13. -/
theorem prop37_classNumberBound :
    ∃ C_class : ℝ, C_class > 0 ∧
    ∀ (K : Type*) [Field K] [NumberField K],
      (Fintype.card (ClassGroup (𝓞 K)) : ℝ) ≤
        (max 2 (rootDiscr K)) ^ (C_class * Module.finrank ℚ K) := by
  exact minkowski_class_number_bound

end UnitDistance.NumberTheory
