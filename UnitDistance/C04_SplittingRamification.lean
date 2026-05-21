import Mathlib
import UnitDistance.C03_BasicFieldConventions

set_option linter.style.longLine false

namespace UnitDistance.NumberTheory

open NumberField

/-!
# Definition A.2: Splitting, Ramification, and Unramified Extensions

Let M/F be a finite extension of number fields and let p be a finite prime (nonzero prime ideal)
of F. This file formalizes the notions of:
- Ramification index e(P/p) = Ideal.ramificationIdx p P  (uses Algebra instance implicitly)
- Unramified primes (e(P/p) = 1 for all P | p)
- Completely split primes (exactly [M:F] primes above p, all with e=f=1)
- Infinite (Archimedean) ramification (real place ramifies iff it extends to complex place)
- Everywhere unramified extensions (unramified at all finite AND infinite places)
-/

variable (F M : Type*) [Field F] [Field M] [Algebra F M] [NumberField F] [NumberField M]

/-- A finite prime p of F is unramified in M/F if the ramification index e(P/p) = 1
for every prime ideal P of 𝓞 M lying above p.

Here `Ideal.ramificationIdx p P` uses the `Algebra (𝓞 F) (𝓞 M)` instance (induced from
`Algebra F M`) and is the multiplicity of P in the factorization of p · 𝓞 M. -/
def IsUnramifiedPrime (p : Ideal (𝓞 F)) : Prop :=
  ∀ P : Ideal (𝓞 M), P.IsPrime → P.LiesOver p →
    Ideal.ramificationIdx p P = 1

/-- A finite prime p of F splits completely in M/F if:
  (a) the number of prime ideals of 𝓞 M lying above p equals [M : F],
  (b) each such P has ramification index e(P/p) = 1, and
  (c) each such P has inertia degree f(P/p) = [𝓞_M/P : 𝓞_F/p] = 1.
Equivalently: pO_M = P₁ · … · P_{[M:F]} with all Pᵢ distinct. -/
def IsCompletelySplit (p : Ideal (𝓞 F)) : Prop :=
  Set.ncard (p.primesOver (𝓞 M)) = Module.finrank F M ∧
  ∀ P : Ideal (𝓞 M), P.IsPrime → P.LiesOver p →
    Ideal.ramificationIdx p P = 1 ∧
    Ideal.inertiaDeg p P = 1

/-- For a rational prime q and a number field L with [L:ℚ] = d, the prime q splits completely
in L if there are exactly d prime ideals P₁, …, P_d of 𝓞 L lying above q, each with
ramification index e = 1 and inertia degree f = 1 (so O_L/Pᵢ ≅ 𝔽_q for all i). -/
def IsCompletelySplitRational (q : ℕ) (_hq : q.Prime) (L : Type*) [Field L] [NumberField L]
    [Algebra ℚ L] : Prop :=
  let p : Ideal ℤ := Ideal.span {(q : ℤ)}
  Set.ncard (p.primesOver (𝓞 L)) = Module.finrank ℚ L ∧
  ∀ P : Ideal (𝓞 L), P.IsPrime → P.LiesOver p →
    Ideal.ramificationIdx p P = 1 ∧
    Ideal.inertiaDeg p P = 1

/-!
## Infinite (Archimedean) Ramification

Each embedding σ : F ↪ ℂ gives an infinite place of F. An infinite place w of M
(corresponding to an embedding M ↪ ℂ) is **unramified** over F if
`NumberField.InfinitePlace.IsUnramified F w` holds, i.e., the multiplicity of w|_F equals
the multiplicity of w. An infinite place w of M is **ramified** over F iff it is a complex
place lying over a real place of F.

Key Mathlib facts:
- `NumberField.InfinitePlace.not_isUnramified_iff`: w is ramified iff w.IsComplex ∧ (w|_F).IsReal
- A totally real extension of a totally real field has no infinite ramification.
- `IsUnramifiedAtInfinitePlaces F M`: all infinite places of M are unramified over F.
-/

/-- An extension M/F is everywhere unramified if it is unramified at all finite primes
and at all infinite (Archimedean) places.

- Unramified at all finite primes: e(P/p) = 1 for every nonzero prime p of 𝓞 F and
  every prime P of 𝓞 M lying above p.
- Unramified at all infinite places: every infinite place of M is unramified over F,
  equivalently, no complex place of M lies above a real place of F. -/
def IsEverywhereUnramified : Prop :=
  (∀ p : Ideal (𝓞 F), p.IsMaximal →
    ∀ P : Ideal (𝓞 M), P.IsPrime → P.LiesOver p →
      Ideal.ramificationIdx p P = 1) ∧
  IsUnramifiedAtInfinitePlaces F M

end UnitDistance.NumberTheory
