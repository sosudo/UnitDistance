import Mathlib
import UnitDistance.C02_AdmissibleDatum
import UnitDistance.C03_BasicFieldConventions
import UnitDistance.C20_MinkowskiLattice
import UnitDistance.C29_Lemma25

set_option linter.style.longLine false

namespace UnitDistance

open Real

/-- Lemma 2.6 (Packing bound): Given the setup from Lemmas 2.4 and 2.5,
    let n = |P| = |X| = N_a. Then n ≤ exp(B · f),
    where B = 2 · log(4RD), D = Q² = (∏ qᵢ)². -/
theorem lemma26_packingBound
    (d : AdmissibleDatum) [NeZero d.f]
    (mld : MinkowskiLatticeData d)
    (γ R : ℝ) (hR : R > 1 / 2) (hγpos : γ > 0)
    (a : Fin d.f → ℂ)
    (hcoset_nonempty : (cosetCount d mld a R : ℝ) > 0)
    (hcoset_good : (unitPairCount d mld a R : ℝ) ≥
                    Real.exp (γ * d.f / 2) * cosetCount d mld a R) :
    let D := (d.Q : ℝ) ^ 2
    let B := 2 * Real.log (4 * R * D)
    let n := cosetCount d mld a R
    (n : ℝ) ≤ Real.exp (B * d.f) := by
  sorry

end UnitDistance
