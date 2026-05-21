import Mathlib
import UnitDistance.C02_AdmissibleDatum
import UnitDistance.C20_MinkowskiLattice
import UnitDistance.C21_NormOneSetU

set_option linter.style.longLine false

namespace UnitDistance

open Real

/-- Lemma 2.4 (Coset Averaging): Given an admissible datum, a class number bound H,
    and γ = t · log 2 - log H > 0, for all sufficiently large R there exists
    a coset a + Λ of the Minkowski lattice such that
    E_a ≥ exp(γ · f / 2) · N_a,
    i.e., the unit-pair count exceeds the coset count by a factor of e^{γf/2}.

    Here f = [L:ℚ], E_a counts ordered pairs in the coset whose difference lies in Φ(U),
    and N_a counts the coset points in the sup-norm ball B_R. -/
axiom lemma24_cosetAveraging
    (d : AdmissibleDatum) [NeZero d.f] (H : ℝ) (hH : H > 0)
    (γ : ℝ) (hγ : γ = d.t * Real.log 2 - Real.log H) (hγpos : γ > 0)
    (mld : MinkowskiLatticeData d)
    (U_size : (mld.U.card : ℝ) ≥ Real.exp (γ * d.f))
    (R : ℝ) (hR_pos : R > 1 / 2)
    (hR_large : Real.log (discOverlapRatio R) > -(γ / 2)) :
    ∃ a : Fin d.f → ℂ,
      (cosetCount d mld a R : ℝ) > 0 ∧
      (unitPairCount d mld a R : ℝ) ≥
        Real.exp (γ * d.f / 2) * (cosetCount d mld a R : ℝ)

end UnitDistance
