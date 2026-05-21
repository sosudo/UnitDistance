import Mathlib
import UnitDistance.C01_UnitDistanceFunctions
import UnitDistance.C31_Theorem23
import UnitDistance.C32_Prop38

set_option linter.style.longLine false

namespace UnitDistance

open Real

/-- Theorem 1.1 (Main Result): There exists an absolute constant δ > 0 and
    infinitely many positive integers n such that ν(n) ≥ n^{1+δ}.
    This disproves the Erdős unit-distance conjecture.
    Proof: Apply prop38_fieldConstruction to get a sequence of admissible data with γ > 0,
    then apply theorem23_admissibleToNu to obtain δ and infinitely many n. -/
theorem theorem11_mainResult :
    ∃ δ : ℝ, δ > 0 ∧
      ∃ nseq : ℕ → ℕ,
        (∀ j, nseq j < nseq (j+1)) ∧
        (∀ j, (maxUnitDistancePairs (nseq j) : ℝ) ≥ (nseq j : ℝ) ^ (1 + δ)) := by
  -- Get the field construction from Proposition 3.8, instantiated at universe level 0
  obtain ⟨ℓ₀, hprop38⟩ := UnitDistance.NumberTheory.prop38_fieldConstruction.{0, 0}
  -- Pick ℓ = max(ℓ₀, 11) so that t = (ℓ-1)²/100 ≥ 1 (since (11-1)²/100 = 1)
  let ℓ : ℕ := max ℓ₀ 11
  have hℓ_ge : ℓ₀ ≤ ℓ := Nat.le_max_left _ _
  have hℓ11 : 11 ≤ ℓ := Nat.le_max_right _ _
  -- Apply prop38 at this ℓ; obtain all components
  obtain ⟨H, hH1, hγpos, data, hdata_t, -, hf_grows, -, hclassnum, hprimes⟩ :=
    hprop38 ℓ hℓ_ge
  -- Establish t ≥ 1 where t = (ℓ-1)²/100
  have ht : 1 ≤ (ℓ - 1) ^ 2 / 100 := by
    have h1 : 10 ≤ ℓ - 1 := by omega
    have h2 : 100 ≤ (ℓ - 1) ^ 2 := by nlinarith
    omega
  -- Apply Theorem 2.3 with t = (ℓ-1)²/100, H, γ = t·log2 - logH
  -- γ is the Nat cast of t times log2 minus log H
  refine theorem23_admissibleToNu.{0, 0} _ ht H (by linarith) _ rfl hγpos data hdata_t ?_ hf_grows hclassnum
  -- Prove shared primes: (data j).primes agrees with (data 0).primes on Fin t
  intro j i
  exact hprimes j (hdata_t j) (hdata_t 0) i

end UnitDistance
