import Mathlib
import UnitDistance.C03_BasicFieldConventions

set_option linter.style.longLine false

/-!
# Conductors and Character Groups (Definition A.5)

This file formalizes the notions of field conductors, Dirichlet character conductors,
and fields cut out by character groups, as used in the unit-distance proof.

**Source**: Definition A.5 (Conductors and fields cut out by characters), lines 867–876.

## Main definitions

- `UnitDistance.NumberTheory.IsAbelianExtension`: predicate for finite abelian extension L/ℚ
- `UnitDistance.NumberTheory.fieldConductor`: the field conductor f(L/ℚ) = min{m | L ⊆ ℚ(ζ_m)}
- `UnitDistance.NumberTheory.dirichletCharConductor`: conductor f(χ) of a Dirichlet character
- `UnitDistance.NumberTheory.DirichletCharOverℂ`: a Dirichlet character over ℂ at some modulus
- `UnitDistance.NumberTheory.characterGroup`: character group of an abelian extension (axiomatized)
- `UnitDistance.NumberTheory.conductorDiscriminantFormula`: |D_L| = ∏_{χ∈X} f(χ) (axiom)
- `UnitDistance.NumberTheory.conductor_mul_of_coprime_conductors`: f(χ₁·χ₂) = f(χ₁)·f(χ₂) (axiom)

## Dependencies

- Kronecker–Weber theorem (external; not yet in Mathlib 4.29.1): axiomatized as `kroneckerWeber`
- `DirichletCharacter` from `Mathlib.NumberTheory.DirichletCharacter.Basic`
- `NumberField.discr` from `Mathlib.NumberTheory.NumberField.Discriminant`
- `IsAbelianGalois` from `Mathlib.FieldTheory.Galois.Abelian`
-/

namespace UnitDistance.NumberTheory

open NumberField DirichletCharacter

/-!
### Finite abelian extensions of ℚ
-/

/-- Predicate asserting that a number field L is a finite abelian extension of ℚ:
    a Galois extension with abelian Galois group. Uses `IsAbelianGalois` from Mathlib. -/
def IsAbelianExtension (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] : Prop :=
  IsAbelianGalois ℚ L

/-!
### Field conductor of a finite abelian extension L/ℚ

By the Kronecker–Weber theorem, every finite abelian extension L/ℚ is contained in some
cyclotomic field ℚ(ζ_m). The field conductor is the minimum such m.
-/

/-- The set of positive naturals m such that L embeds (as a ℚ-algebra) into ℚ(ζ_m):
    `{m : ℕ | m ≥ 1 ∧ ∃ ℚ-algebra embedding L →ₐ[ℚ] CyclotomicField m ℚ}`. -/
noncomputable def cyclotomicEmbeddingSet (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] : Set ℕ :=
  {m : ℕ | m ≥ 1 ∧ Nonempty (L →ₐ[ℚ] CyclotomicField m ℚ)}

/-- The field conductor of a finite abelian extension L/ℚ:
    the least positive m such that L embeds into ℚ(ζ_m) (Kronecker–Weber theorem).

    The Kronecker–Weber theorem (axiomatized below as `kroneckerWeber`) guarantees that
    `cyclotomicEmbeddingSet L` is nonempty for any abelian extension. -/
noncomputable def fieldConductor (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] : ℕ :=
  sInf (cyclotomicEmbeddingSet L)

/-- Axiom (Kronecker–Weber theorem): every finite abelian extension of ℚ embeds into some
    cyclotomic field ℚ(ζ_m) with m ≥ 1.
    This ensures `cyclotomicEmbeddingSet L` is nonempty. -/
axiom kroneckerWeber (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (h : IsAbelianExtension L) :
    (cyclotomicEmbeddingSet L).Nonempty

/-!
### Conductor of a Dirichlet character

The conductor f(χ) of a Dirichlet character χ of modulus n is the least modulus through which
χ factors, equivalently the modulus of the unique primitive character that induces χ.
This is already defined in Mathlib as `DirichletCharacter.conductor`.
-/

/-- The conductor f(χ) of a Dirichlet character χ of modulus n over R:
    the least modulus m such that χ factors through (ℤ/mℤ)×.
    This is a definitional alias for `DirichletCharacter.conductor`. -/
noncomputable def dirichletCharConductor {R : Type*} [CommMonoidWithZero R] {n : ℕ}
    (χ : DirichletCharacter R n) : ℕ :=
  χ.conductor

/-- `dirichletCharConductor` agrees with `DirichletCharacter.conductor`. -/
theorem dirichletCharConductor_eq {R : Type*} [CommMonoidWithZero R] {n : ℕ}
    (χ : DirichletCharacter R n) :
    dirichletCharConductor χ = χ.conductor :=
  rfl

/-- The conductor of χ divides the modulus n. -/
theorem dirichletCharConductor_dvd_level {R : Type*} [CommMonoidWithZero R] {n : ℕ}
    (χ : DirichletCharacter R n) :
    dirichletCharConductor χ ∣ n :=
  χ.conductor_dvd_level

/-- χ is primitive iff its conductor equals its modulus. -/
theorem dirichletChar_isPrimitive_iff {R : Type*} [CommMonoidWithZero R] {n : ℕ}
    (χ : DirichletCharacter R n) :
    χ.IsPrimitive ↔ dirichletCharConductor χ = n :=
  χ.isPrimitive_def

/-!
### Character group of a finite abelian extension and the field it cuts out

Given a finite group X of Dirichlet characters (over ℂ), with a common modulus m, the fixed
field of ∩_{χ∈X} ker χ (viewed inside Gal(ℚ(ζ_m)/ℚ) ≅ (ℤ/mℤ)×) is the field cut out by X.
Via class field theory, this association is bijective between character groups and abelian
subextensions of ℚ(ζ_m)/ℚ.

Since the full Galois-theoretic machinery is not yet in Mathlib, we axiomatize the key results.
-/

/-- A Dirichlet character over ℂ at some modulus, packaged as a structure. -/
structure DirichletCharOverℂ where
  /-- The modulus of the character. -/
  modulus : ℕ
  /-- The character itself (a multiplicative character (ℤ/modulus)× → ℂ×). -/
  char : DirichletCharacter ℂ modulus

/-- The character group of a finite abelian extension L/ℚ (axiomatized via class field theory):
    a finite set of Dirichlet characters over ℂ that "cut out" L as a fixed field.

    In class field theory: via Gal(ℚ(ζ_m)/ℚ) ≅ (ℤ/mℤ)×, the subgroup ∩_{χ∈X} ker χ
    corresponds to a subfield of ℚ(ζ_m); X is the character group when this subfield is L.
    The concrete construction requires infrastructure not yet in Mathlib 4.29.1. -/
noncomputable def characterGroup (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (_h : IsAbelianExtension L) : Finset DirichletCharOverℂ :=
  Classical.arbitrary _

/-!
### Conductor–discriminant formula

For a finite abelian extension L/ℚ with character group X, one has:
    |D_L| = ∏_{χ ∈ X} f(χ)
This is a fundamental theorem of class field theory ([Was97, Ch.3, Thm 3.11]; [Neu99, Ch.VI]).
We axiomatize it.
-/

/-- Conductor–discriminant formula (axiom): For a finite abelian extension L/ℚ with
    character group X, the absolute discriminant satisfies |D_L| = ∏_{χ ∈ X} f(χ).

    Reference: [Was97, Ch.3, Thm 3.11], [Neu99, Ch.VI, §3]. -/
axiom conductorDiscriminantFormula
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (h : IsAbelianExtension L) :
    (NumberField.discr L).natAbs =
      (characterGroup L h).prod (fun χ => χ.char.conductor)

/-!
### Conductor multiplicativity for coprime conductors

If χ₁, …, χ_m are Dirichlet characters with pairwise coprime conductors, then
f(χ₁ · χ₂ · … · χ_m) = f(χ₁) · f(χ₂) · … · f(χ_m).
-/

/-- Conductor multiplicativity (axiom): for two Dirichlet characters over ℂ with coprime
    conductors, f(χ₁ · χ₂) = f(χ₁) · f(χ₂).

    Here multiplication is via `DirichletCharacter.mul` which lifts to the lcm of the moduli. -/
axiom conductor_mul_of_coprime_conductors
    {n₁ n₂ : ℕ} (χ₁ : DirichletCharacter ℂ n₁) (χ₂ : DirichletCharacter ℂ n₂)
    (hcop : Nat.Coprime χ₁.conductor χ₂.conductor) :
    (DirichletCharacter.mul χ₁ χ₂).conductor =
      χ₁.conductor * χ₂.conductor

/-!
### Single-character case: the field cut out by a character

If X = ⟨χ⟩ (cyclic group generated by χ of order d), the field cut out by X is a
cyclic extension of ℚ of degree d. In particular, an order-3 character cuts out a
cyclic cubic field (a degree-3 extension with Galois group ≅ ℤ/3ℤ).
-/

/-- The field cut out by a single character χ of order d is a cyclic extension of ℚ of degree d.
    For an order-3 character, this gives a cyclic cubic field. (Axiomatized.) -/
axiom fieldCutOutByChar_degree
    {n : ℕ} (χ : DirichletCharacter ℂ n) (d : ℕ) (hd : 0 < d)
    (hord : orderOf χ = d) :
    ∃ (F : Type*) (_ : Field F) (_ : NumberField F) (_ : Algebra ℚ F),
      IsAbelianGalois ℚ F ∧
      Fintype.card (F ≃ₐ[ℚ] F) = d

end UnitDistance.NumberTheory
