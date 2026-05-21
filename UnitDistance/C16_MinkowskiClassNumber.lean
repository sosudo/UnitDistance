import Mathlib
import UnitDistance.C08_Discriminants

set_option linter.style.longLine false

open NumberField

namespace UnitDistance.NumberTheory

/-- Minkowski class number bound (Proposition A.13):
    There is an absolute constant C_class > 0 such that for every number field K,
    h(K) = |ClassGroup(𝓞 K)| ≤ max{2, rd(K)}^{C_class · [K:ℚ]}. -/
axiom minkowski_class_number_bound :
    ∃ C_class : ℝ, C_class > 0 ∧
    ∀ (K : Type*) [Field K] [NumberField K],
      (Fintype.card (ClassGroup (𝓞 K)) : ℝ) ≤
        (max 2 (rootDiscriminant K)) ^ (C_class * Module.finrank ℚ K)

end UnitDistance.NumberTheory
