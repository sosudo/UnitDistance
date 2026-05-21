import Mathlib
import UnitDistance.C07_ConductorsCharacters
import UnitDistance.C08_Discriminants

set_option linter.style.longLine false

namespace UnitDistance.NumberTheory

/-- For a prime r ≡ 1 (mod 3), the unique cyclic cubic subfield of ℚ(ζ_r)
    is totally real with conductor r. We state: there is a totally real cubic
    number field F with [F:ℚ] = 3 and conductor r, where the conductor is
    fieldConductor F (the least m ≥ 1 with F ⊆ ℚ(ζ_m)). -/
axiom cyclotomic_cubic_subfield_exists (r : ℕ) (hr : r.Prime) (hmod : r % 3 = 1) :
    ∃ (F : Type*) [Field F] [NumberField F] [Algebra ℚ F] [NumberField.IsTotallyReal F],
      Module.finrank ℚ F = 3 ∧ fieldConductor F = r

/-- Conductor-discriminant formula for finite abelian extensions of ℚ.
    |D_L| = ∏_{χ ∈ char_group(L/ℚ)} f(χ). -/
axiom conductor_discriminant_formula_C14
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] (h : IsAbelianExtension L) :
    (NumberField.discr L).natAbs = (characterGroup L h).prod (fun χ => χ.char.conductor)

/-- Conductor multiplicativity for characters with pairwise coprime conductors. -/
axiom conductor_mul_coprime_chars_C14
    {n₁ n₂ : ℕ} (χ₁ : DirichletCharacter ℂ n₁) (χ₂ : DirichletCharacter ℂ n₂)
    (hcop : Nat.Coprime χ₁.conductor χ₂.conductor) :
    (DirichletCharacter.mul χ₁ χ₂).conductor =
      χ₁.conductor * χ₂.conductor

end UnitDistance.NumberTheory
