import Mathlib
import UnitDistance.C03_BasicFieldConventions
import UnitDistance.C04_SplittingRamification

set_option linter.style.longLine false

namespace UnitDistance.NumberTheory

open NumberField

/-!
# Frobenius Elements in Galois Extensions of Number Fields

Let N/K be a finite Galois extension of number fields and p an unramified prime of K.
For any prime P of 𝓞 N lying above p, the Frobenius element Frob_{P/p} is the unique
element σ ∈ Gal(N/K) such that σ(x) ≡ x^{|𝓞_K/p|} (mod P) for all x ∈ 𝓞 N.

The Frobenius element exists in Mathlib as `arithFrobAt` from `Mathlib.RingTheory.Frobenius`.
The definition `IsArithFrobAt R σ Q` says σ is a Frobenius element at Q over R.

The key fact we need is: p splits completely in N if and only if for every prime P | p,
the Frobenius element Frob_{P/p} is the identity in Gal(N/K).
-/

variable (K N : Type*) [Field K] [Field N] [Algebra K N]
  [NumberField K] [NumberField N] [IsGalois K N]

/-!
## Frobenius Elements via Mathlib

Mathlib provides `arithFrobAt` (from `RingTheory.Frobenius`):
  `arithFrobAt R G Q : G`
for a group G acting on a ring S with fixed subring R, and Q a prime ideal of S
with finite residue field.

For a Galois extension N/K of number fields:
- R = 𝓞 K (ring of integers of K)
- S = 𝓞 N (ring of integers of N)
- G = Gal(N/K) acting on 𝓞 N (via the induced action from the Galois action on N)
- Q = a prime P of 𝓞 N with finite residue field (guaranteed since 𝓞 N/P is a finite field)
-/

/-- The Frobenius element in Gal(N/K) at a prime P of 𝓞 N lying above an unramified prime p
of 𝓞 K. This is the unique σ ∈ Gal(N/K) satisfying σ(x) ≡ x^{N(p)} (mod P) for all x ∈ 𝓞 N,
where N(p) = |𝓞_K / p| is the norm of p.

We use Mathlib's `arithFrobAt` from `Mathlib.RingTheory.Frobenius`. -/
noncomputable def FrobeniusElement
    (P : Ideal (𝓞 N)) [P.IsPrime] [Finite ((𝓞 N) ⧸ P)] :
    Gal(N/K) :=
  arithFrobAt (𝓞 K) Gal(N/K) P

/-- The Frobenius element at P satisfies the defining property:
σ(x) ≡ x^{|𝓞_K / (P ∩ 𝓞_K)|} (mod P) for all x ∈ 𝓞 N. -/
theorem FrobeniusElement_isArithFrob
    (P : Ideal (𝓞 N)) [P.IsPrime] [Finite ((𝓞 N) ⧸ P)] :
    IsArithFrobAt (𝓞 K) (FrobeniusElement K N P) P :=
  IsArithFrobAt.arithFrobAt (R := 𝓞 K) (G := Gal(N/K)) (Q := P)

/-!
## The Splitting Criterion via Frobenius

The key number-theoretic fact: a prime p of K splits completely in N if and only if the
Frobenius element Frob_{P/p} is the identity in Gal(N/K) for every (equivalently, some)
prime P of 𝓞 N lying above p.

Since Mathlib does not yet provide this theorem for number fields in full generality
(the connection between `IsCompletelySplit` / `IsUnramifiedPrime` from C04 and the
Frobenius criterion), we axiomatize it.
-/

/-- A prime p of K splits completely in N iff the Frobenius element at every prime P | p
is the identity in Gal(N/K). This is the fundamental Frobenius splitting criterion.

Concretely: p splits completely (e = f = 1 for all P | p, with exactly [N:K] primes above p)
if and only if Frob_{P/p} = 1 for all P lying over p. -/
axiom isCompletelySplit_iff_frobenius_eq_one
    (p : Ideal (𝓞 K)) (hp : p.IsPrime) (hne : p ≠ ⊥) :
    IsCompletelySplit K N p ↔
    ∀ (P : Ideal (𝓞 N)) (_ : P.IsPrime) (_ : P ≠ ⊥) (_ : P.LiesOver p)
      (_ : Finite ((𝓞 N) ⧸ P)),
      FrobeniusElement K N P = 1

end UnitDistance.NumberTheory
