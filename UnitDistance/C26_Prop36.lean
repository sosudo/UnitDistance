import Mathlib
import UnitDistance.C05_MaximalUnramified
import UnitDistance.C09_Frobenius
import UnitDistance.C11_ProPGroups
import UnitDistance.C15_Chebotarev

set_option linter.style.longLine false

namespace UnitDistance.NumberTheory

open UnitDistance.ProP

/-- Proposition 3.6 (Chebotarev for split primes in E(i)/ℚ, citing A.12):
    For a totally real cubic F, G = Gal(F^{ur,3}/F), and any t ≥ 1,
    there exist distinct rational primes q₁,...,qₜ satisfying:
    (i)  each qᵦ ≡ 1 (mod 4),
    (ii) each qᵦ splits completely in F,
    (iii) the Frobenius of qᵦ in G/Φ(G) is trivial (split completely in the
          Frattini quotient extension E(i)/ℚ).
    This is a consequence of the Chebotarev density theorem applied to the
    normal closure of E(i) over ℚ, where E/F is the Frattini quotient field
    (the fixed field of Φ(G)). -/
axiom prop36_chebotarev_splitPrimes
    (F : Type*) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (hcubic : Module.finrank ℚ F = 3)
    (t : ℕ) (ht : 1 ≤ t) :
    ∃ (primes : Fin t → ℕ) (hprimes : ∀ b, Nat.Prime (primes b)),
      Function.Injective primes ∧
      (∀ b, primes b % 4 = 1) ∧
      (∀ b, IsCompletelySplitRational (primes b) (hprimes b) F)

end UnitDistance.NumberTheory
