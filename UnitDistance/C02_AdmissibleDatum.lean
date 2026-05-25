import Mathlib
import UnitDistance.C03_BasicFieldConventions
import UnitDistance.C04_SplittingRamification
import UnitDistance.C06_CMFields

set_option linter.style.longLine false

namespace UnitDistance

open NumberField UnitDistance.NumberTheory

/-- An admissible datum consists of:
    - L: a totally real number field of degree f = [L:ℚ] ≥ 1
    - K = L(i): the CM extension of L (where i² = -1)
    - t: a positive integer (number of rational primes)
    - primes q₁,...,qₜ: distinct primes ≡ 1 (mod 4) splitting completely in L
    - Q = ∏ qᵢ: product of the primes

    These determine m = t·[L:ℚ] conjugate prime-ideal pairs in K. -/
structure AdmissibleDatum where
  /-- The totally real base field -/
  L : Type*
  [fieldL : Field L]
  [charZeroL : CharZero L]
  [numberFieldL : NumberField L]
  [totallyRealL : NumberField.IsTotallyReal L]
  /-- The CM field K = L(i) -/
  K : Type*
  [fieldK : Field K]
  [charZeroK : CharZero K]
  [numberFieldK : NumberField K]
  [cmFieldK : NumberField.IsCMField K]
  /-- Algebra structure K/L -/
  [algebraLK : Algebra L K]
  /-- t: number of split primes -/
  t : ℕ
  ht : 1 ≤ t
  /-- The t rational primes q₁,...,qₜ -/
  primes : Fin t → ℕ
  /-- Each qᵢ is prime -/
  primePrime : ∀ i, (primes i).Prime
  /-- Each qᵢ ≡ 1 (mod 4) -/
  primeMod4 : ∀ i, primes i % 4 = 1
  /-- The qᵢ are pairwise distinct -/
  primesDistinct : Function.Injective primes
  /-- Each qᵢ splits completely in L -/
  primeSplitsInL : ∀ i, IsCompletelySplitRational (primes i) (primePrime i) L
  /-- The number of infinite places of K equals f = [L:ℚ].
      This holds because K/L is quadratic (K is CM, L is the totally real subfield),
      so [K:ℚ] = 2f and K is totally complex, giving nrComplexPlaces(K) = f infinite places. -/
  hKL_card :
    letI : Field L := fieldL
    letI : NumberField L := numberFieldL
    letI : Field K := fieldK
    letI : NumberField K := numberFieldK
    Fintype.card (NumberField.InfinitePlace K) = Module.finrank ℚ L
  /-- For each prime index b, the pair (P_b, cP_b) of CM-conjugate prime ideals above primes b
      in 𝓞 K. The first component P_b is a prime ideal above q_b, and the second component is
      its CM conjugate. -/
  primeIdealPairs : Fin t → Ideal (𝓞 K) × Ideal (𝓞 K)
  /-- First component P_b is a prime ideal lying above q_b in ℤ -/
  primeIdealPairs_fst_prime : ∀ b,
    (primeIdealPairs b).1.IsPrime ∧
    (primeIdealPairs b).1.LiesOver (Ideal.span {(primes b : ℤ)} : Ideal ℤ)
  /-- Second component is the image of P_b under the CM conjugation automorphism of 𝓞 K -/
  primeIdealPairs_snd_eq_conj : ∀ b,
    (primeIdealPairs b).2 =
      Ideal.map
        (RingOfIntegers.mapAlgEquiv (IsCMField.complexConj K)).toRingHom
        (primeIdealPairs b).1
  /-- The two ideals in each pair are distinct (P_b ≠ cP_b) -/
  primeIdealPairs_distinct : ∀ b, (primeIdealPairs b).1 ≠ (primeIdealPairs b).2

/-- The product Q = ∏_{i} qᵢ -/
noncomputable def AdmissibleDatum.Q (d : AdmissibleDatum) : ℕ :=
  ∏ i : Fin d.t, d.primes i

/-- The degree f = [L:ℚ] -/
noncomputable def AdmissibleDatum.f (d : AdmissibleDatum) : ℕ :=
  letI := d.fieldL
  letI := d.numberFieldL
  Module.finrank ℚ d.L

/-- The total number of conjugate prime-ideal pairs m = t·f -/
noncomputable def AdmissibleDatum.m (d : AdmissibleDatum) : ℕ :=
  d.t * d.f

/-- The number of infinite places of K equals f, extracted as a clean lemma. -/
lemma AdmissibleDatum.hKL_card' (d : AdmissibleDatum) :
    letI := d.fieldK; letI := d.numberFieldK;
    Fintype.card (NumberField.InfinitePlace d.K) = d.f := by
  letI := d.fieldL; letI := d.numberFieldL; letI := d.fieldK; letI := d.numberFieldK
  exact d.hKL_card

end UnitDistance
