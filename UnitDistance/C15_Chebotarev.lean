import Mathlib
import UnitDistance.C09_Frobenius

set_option linter.style.longLine false

namespace UnitDistance.NumberTheory

/-- Chebotarev density theorem (Proposition A.12):
    For any finite Galois extension N/ℚ and any σ ∈ Gal(N/ℚ), there are
    infinitely many rational primes q (outside finitely many ramified ones) with
    Frobenius conjugacy class equal to [σ] in Gal(N/ℚ). Concretely: there exist
    infinitely many primes q such that some prime P of 𝓞 N above q has
    FrobeniusElement P = σ in Gal(N/ℚ).

    Reference: [Neu99, Chapter VII, §13], [Tsc26].
    Mathlib gap: algebraic proof requires L-functions, Dirichlet series, and the
    analytic density of prime ideals in each Frobenius class — not yet in Mathlib.
    is_assumption: true (permitted axiom in UNITY.md: "Chebotarev density for number fields"). -/
axiom chebotarev_density
    (N : Type*) [Field N] [NumberField N] [Algebra ℚ N] [IsGalois ℚ N]
    (σ : N ≃ₐ[ℚ] N) :
    Set.Infinite {q : ℕ | q.Prime ∧
      ∃ (P : Ideal (NumberField.RingOfIntegers N))
        (_ : P.IsPrime)
        (_ : Finite ((NumberField.RingOfIntegers N) ⧸ P)),
        P.LiesOver (Ideal.span {(q : ℤ)} : Ideal ℤ) ∧
        FrobeniusElement ℚ N P = σ}

end UnitDistance.NumberTheory
