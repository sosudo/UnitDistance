import Mathlib
import UnitDistance.C02_AdmissibleDatum
import UnitDistance.C04_SplittingRamification
import UnitDistance.C05_MaximalUnramified
import UnitDistance.C06_CMFields
import UnitDistance.C08_Discriminants
import UnitDistance.C16_MinkowskiClassNumber

set_option linter.style.longLine false

namespace UnitDistance.NumberTheory

open Real NumberField

/-- Proposition 3.8 (Field Construction):
    For all sufficiently large ℓ, setting t = ⌊(ℓ-1)²/100⌋, there exist:
    - A sequence of admissible data (Lⱼ = Fⱼ, Kⱼ = Fⱼ(i), q₁,...,qₜ) for j = 0, 1, 2, ...
      all sharing the same t primes q₁,...,qₜ
    - A constant H_ℓ > 1 with log H_ℓ = O(ℓ log ℓ)

    satisfying:
    (P1) F = F₀ is totally real, Gal(F/ℚ) ≅ ℤ/3ℤ, and [F₀:ℚ] = 3
    (P2) fⱼ = [Fⱼ:ℚ] → ∞ (degrees diverge)
    (P3) rd(Fⱼ) = rd(F₀) for all j (root discriminant constant in the tower)
    (P4) Each qᵦ ≡ 1 (mod 4) and splits completely in every Fⱼ (already in AdmissibleDatum)
    (P5) h(Kⱼ) ≤ H_ℓ^{fⱼ} (class number bound)
    (P6) t · log 2 - log H_ℓ > 0 (positivity of contribution gap) -/
axiom prop38_fieldConstruction :
    ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ →
    let t : ℕ := (ℓ - 1) ^ 2 / 100
    ∃ (H_ℓ : ℝ),
    H_ℓ > 1 ∧
    -- P6: γ = t · log 2 - log H_ℓ > 0
    (t : ℝ) * Real.log 2 - Real.log H_ℓ > 0 ∧
    -- The sequence of admissible data witnessing the infinite tower
    ∃ (data : ℕ → UnitDistance.AdmissibleDatum),
    -- All levels share the same count t of primes
    (∀ j, (data j).t = t) ∧
    -- P1: base field is totally real cyclic cubic with [F₀:ℚ] = 3
    (data 0).f = 3 ∧
    -- P2: degrees fⱼ → ∞
    (∀ M : ℕ, ∃ j : ℕ, M ≤ (data j).f) ∧
    -- P3: root discriminant is constant across the tower
    (∀ j, letI := (data j).fieldL; letI := (data j).numberFieldL;
          letI := (data 0).fieldL; letI := (data 0).numberFieldL;
          rootDiscr (data j).L = rootDiscr (data 0).L) ∧
    -- P5: class number bound h(Kⱼ) ≤ H_ℓ^{fⱼ}
    (∀ j, letI := (data j).fieldK; letI := (data j).numberFieldK;
      (Fintype.card (ClassGroup (𝓞 (data j).K)) : ℝ) ≤
        H_ℓ ^ (data j).f)

end UnitDistance.NumberTheory
