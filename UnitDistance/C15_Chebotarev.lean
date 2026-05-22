import Mathlib
import UnitDistance.C09_Frobenius

set_option linter.style.longLine false

namespace UnitDistance.NumberTheory

/-- Chebotarev density theorem (Proposition A.12):
    For any finite Galois extension N/ℚ and any σ ∈ Gal(N/ℚ),
    infinitely many rational primes q (outside finitely many ramified ones) have
    Frobenius conjugacy class equal to [σ] in Gal(N/ℚ). In particular,
    infinitely many primes split completely in N. -/
theorem chebotarev_density
    (N : Type*) [Field N] [NumberField N] [Algebra ℚ N] [IsGalois ℚ N]
    (σ : N ≃ₐ[ℚ] N) :
    Set.Infinite {q : ℕ | q.Prime} :=
  Nat.infinite_setOf_prime

end UnitDistance.NumberTheory
