import Mathlib
import UnitDistance.C01_UnitDistanceFunctions
import UnitDistance.C02_AdmissibleDatum
import UnitDistance.C06_CMFields
import UnitDistance.C20_MinkowskiLattice
import UnitDistance.C28_Lemma24

set_option linter.style.longLine false

namespace UnitDistance

open Real Complex

/-- Lemma 2.5 (Injectivity and ν-bound):
    Given the Minkowski lattice setup from Lemma 2.4, fix a coset a + Λ with
    E_a ≥ exp(γf/2) · N_a. Let X = X_a = (a + Λ) ∩ B_R and P = π₁(X) ⊂ ℂ
    be the first-coordinate projection.

    (a) π₁|_X is injective, so |P| = |X| = N_a.
    (b) ν(P) ≥ (1/2) · exp(γf/2) · |P|,
    where ν(P) counts unordered unit-distance pairs in P ≅ ℝ². -/
theorem lemma25_injectivity_nuBound
    (d : AdmissibleDatum) [NeZero d.f]
    (mld : MinkowskiLatticeData d)
    (H γ R : ℝ) (hH : H > 0) (hγpos : γ > 0) (hR : R > 1 / 2)
    -- The good coset from Lemma 2.4
    (a : Fin d.f → ℂ)
    (hcoset_nonempty : (cosetCount d mld a R : ℝ) > 0)
    (hcoset_good : (unitPairCount d mld a R : ℝ) ≥
                    Real.exp (γ * d.f / 2) * cosetCount d mld a R) :
    let X := cosetBallIntersection d mld a R
    -- (a) First-coordinate projection is injective on X
    -- The projection π₁: ℂ^f → ℂ sends (z₁,...,z_f) ↦ z₁
    let π₁ : (Fin d.f → ℂ) → ℂ := fun z => z ⟨0, Nat.pos_of_ne_zero (NeZero.ne d.f)⟩
    let P := π₁ '' X
    Set.InjOn π₁ X ∧
    -- (b) ν(P) ≥ (1/2) exp(γf/2) |P|
    ∃ Pfin : Finset (EuclideanSpace ℝ (Fin 2)),
      (Pfin.card : ℝ) = Set.ncard P ∧
      (unitDistancePairs Pfin : ℝ) ≥
        (1 / 2) * Real.exp (γ * d.f / 2) * Set.ncard P := by
  sorry

end UnitDistance
