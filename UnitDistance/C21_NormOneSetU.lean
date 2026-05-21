import Mathlib
import UnitDistance.C02_AdmissibleDatum
import UnitDistance.C06_CMFields
import UnitDistance.C08_Discriminants

set_option linter.style.longLine false

namespace UnitDistance

open NumberField Real

set_option maxHeartbeats 800000 in
-- Increased heartbeat limit needed: letI chains in the theorem type require more elaboration
-- time when Lean resolves instances for d.K, d.L from the AdmissibleDatum structure.
/-- Proposition 2.2 (NormOneSetU): Given an admissible datum (L, K, t, q₁,...,qₜ, Q)
    with class number bound h(K) ≤ H^f (where f = [L:ℚ]),
    there exists a finite set U of elements of K such that:
    (i)   Every u ∈ U has relative norm N_{K/L}(u) = 1
          (expressed as Algebra.norm over L equals 1)
    (ii)  Every u ∈ U has ‖σ(u)‖ = 1 for all complex embeddings σ : K → ℂ
    (iii) |U| ≥ exp((t · log 2 - log H) · f)
    (iv)  Every u ∈ U lies in Q^{-2} · O_K, i.e., Q² · u is integral over ℤ

    Here f = [L:ℚ] is the degree of L over ℚ, and Q = ∏ qᵢ is the product of the t split primes. -/
axiom normOneSetU_exists (d : AdmissibleDatum) (H : ℝ) (hH : H > 0)
    (hClassNum : letI := d.fieldK; letI := d.numberFieldK;
      (Fintype.card (ClassGroup (𝓞 d.K)) : ℝ) ≤ H ^ d.f) :
    letI := d.fieldK; letI := d.charZeroK; letI := d.numberFieldK;
    letI := d.cmFieldK; letI := d.algebraLK;
    letI := d.fieldL; letI := d.numberFieldL;
    ∃ U : Finset d.K,
      /- (i) Every u ∈ U has relative norm N_{K/L}(u) = 1 in L -/
      (∀ u ∈ U, Algebra.norm d.L u = 1) ∧
      /- (ii) Every u ∈ U has ‖σ(u)‖ = 1 for all complex embeddings σ : K → ℂ -/
      (∀ u ∈ U, ∀ φ : d.K →+* ℂ, ‖φ u‖ = 1) ∧
      /- (iii) |U| ≥ exp((t · log 2 - log H) · f) -/
      (U.card : ℝ) ≥ Real.exp ((↑d.t * Real.log 2 - Real.log H) * ↑d.f) ∧
      /- (iv) Every u ∈ U lies in Q^{-2} · O_K: Q² · u is integral over ℤ -/
      (∀ u ∈ U, IsIntegral ℤ ((d.Q : d.K) ^ 2 * u))

end UnitDistance
