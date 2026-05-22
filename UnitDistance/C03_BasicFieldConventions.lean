import Mathlib

set_option linter.style.longLine false

namespace UnitDistance.NumberTheory

open NumberField

/-- A rational prime is a natural number satisfying Nat.Prime. -/
abbrev RationalPrime := {p : ℕ // p.Prime}

/-- A finite prime of L is a nonzero prime ideal of 𝓞 L. -/
structure FinitePrime (L : Type*) [Field L] [NumberField L] where
  val : Ideal (𝓞 L)
  isPrime : val.IsPrime
  ne_bot : val ≠ ⊥

/-- L is totally real if every embedding L ↪ ℂ has image in ℝ.
    This is an alias for `NumberField.IsTotallyReal` from Mathlib. -/
abbrev IsTotallyReal (L : Type*) [Field L] [NumberField L] : Prop :=
  NumberField.IsTotallyReal L

end UnitDistance.NumberTheory
