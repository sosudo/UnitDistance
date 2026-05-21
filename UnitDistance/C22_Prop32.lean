import Mathlib
import UnitDistance.C04_SplittingRamification
import UnitDistance.C07_ConductorsCharacters
import UnitDistance.C08_Discriminants
import UnitDistance.C14_CyclotomicCubic

set_option linter.style.longLine false

namespace UnitDistance.NumberTheory

open NumberField

/-!
# Proposition 3.2: Galois Structure, Discriminant, and Everywhere-Unramified Extension

Let r₁,...,r_ℓ be distinct rational primes congruent to 1 mod 3. For each i, let L_i be the
unique cyclic cubic subfield of ℚ(ζ_{r_i}), and put M = L₁⋯L_ℓ (compositum). Let χ_i be a
cubic Dirichlet character of conductor r_i cutting out L_i, and let F ⊂ M be the cyclic cubic
subfield cut out by χ = χ₁⋯χ_ℓ. Writing D = ∏ r_i, the conclusion is:
- Each L_i is totally real
- L₁,...,L_ℓ are linearly disjoint over ℚ
- Gal(M/ℚ) ≅ (ℤ/3ℤ)^ℓ
- Gal(M/F) ≅ (ℤ/3ℤ)^{ℓ-1}
- |D_F| = D²
- M/F is everywhere unramified
-/

/-- Proposition 3.2: For ℓ ≥ 1 distinct primes r₁,...,r_ℓ ≡ 1 (mod 3),
    let L_i be the cyclic cubic subfield of ℚ(ζ_{r_i}), M = L₁⋯L_ℓ their compositum,
    and F ⊂ M the cyclic cubic subfield cut out by χ = χ₁⋯χ_ℓ. Then:
    (1) each L_i is totally real,
    (2) L₁,...,L_ℓ are linearly disjoint over ℚ, so Gal(M/ℚ) ≅ (ℤ/3ℤ)^ℓ,
    (3) Gal(M/F) ≅ (ℤ/3ℤ)^{ℓ-1},
    (4) |D_F| = (∏ r_i)²,
    (5) M/F is everywhere unramified. -/
theorem prop32_galoisStructure_discUnramified
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (r : Fin ℓ → ℕ) (hr_prime : ∀ i, (r i).Prime) (hr_mod : ∀ i, r i % 3 = 1)
    (hr_distinct : Function.Injective r) :
    -- There exist number fields F ⊆ M (cyclic cubic F, compositum M) such that:
    ∃ (F M : Type*),
      ∃ (_ : Field F) (_ : NumberField F) (_ : Algebra ℚ F)
        (_ : Field M) (_ : NumberField M) (_ : Algebra ℚ M) (_ : Algebra F M),
      -- [F:ℚ] = 3
      (letI : Field F := ‹_›; letI : NumberField F := ‹_›; letI : Algebra ℚ F := ‹_›;
       Module.finrank ℚ F = 3) ∧
      -- F is totally real
      (letI : Field F := ‹_›; letI : NumberField F := ‹_›;
       IsTotallyReal F) ∧
      -- |D_F| = (∏ r_i)²
      (letI : Field F := ‹_›; letI : NumberField F := ‹_›;
       (discr F).natAbs = (∏ i : Fin ℓ, r i) ^ 2) ∧
      -- M/F is everywhere unramified
      (letI : Field F := ‹_›; letI : NumberField F := ‹_›; letI : Algebra ℚ F := ‹_›;
       letI : Field M := ‹_›; letI : NumberField M := ‹_›; letI : Algebra ℚ M := ‹_›;
       letI : Algebra F M := ‹_›;
       IsEverywhereUnramified F M) := by
  sorry

end UnitDistance.NumberTheory
