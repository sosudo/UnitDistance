import Mathlib
import UnitDistance.C01_UnitDistanceFunctions
import UnitDistance.C02_AdmissibleDatum
import UnitDistance.C21_NormOneSetU
import UnitDistance.C28_Lemma24
import UnitDistance.C29_Lemma25
import UnitDistance.C210_Lemma26

set_option linter.style.longLine false

namespace UnitDistance

open Real NumberField

/-- Theorem 2.3: Given a sequence of admissible data with fixed primes q₁,...,qₜ,
    degrees f_j → ∞, and class number bound h(K_j) ≤ H^{f_j} with γ = t·log2 - logH > 0,
    there exists δ > 0 and infinitely many n with ν(n) ≥ n^{1+δ}. -/
axiom theorem23_admissibleToNu
    (t : ℕ) (ht : 1 ≤ t)
    (H : ℝ) (hH : H > 0)
    (γ : ℝ) (hγ : γ = t * Real.log 2 - Real.log H) (hγpos : γ > 0)
    -- Sequence of admissible data with fixed primes and growing f_j
    (data : ℕ → AdmissibleDatum)
    (hdata_t : ∀ j, (data j).t = t)
    -- Shared primes: each datum has the same t primes (via hdata_t reindexing)
    (hdata_primes : ∀ j (i : Fin t),
        (data j).primes (i.cast (hdata_t j).symm) = (data 0).primes (i.cast (hdata_t 0).symm))
    (hdata_fGrowing : ∀ M : ℕ, ∃ j, M ≤ (data j).f)
    -- Class number bound
    (hdata_classNum : ∀ j,
      letI := (data j).fieldK
      letI := (data j).numberFieldK
      (Fintype.card (ClassGroup (𝓞 (data j).K)) : ℝ) ≤ H ^ (data j).f) :
    ∃ δ : ℝ, δ > 0 ∧
      ∃ nseq : ℕ → ℕ,
        (∀ j, nseq j < nseq (j+1)) ∧
        (∀ j, (maxUnitDistancePairs (nseq j) : ℝ) ≥ (nseq j : ℝ) ^ (1 + δ))

end UnitDistance
