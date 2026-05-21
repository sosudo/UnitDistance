import Mathlib
import UnitDistance.C02_AdmissibleDatum
import UnitDistance.C21_NormOneSetU

set_option linter.style.longLine false

namespace UnitDistance

open NumberField Real Complex Filter Topology

/-- The Minkowski embedding data for an admissible datum.
    Given d : AdmissibleDatum, this bundles the data needed for the Minkowski lattice
    construction:
    - The embedding Φ : K → ℂ^f using f chosen complex embeddings σ₁,...,σ_f of K
    - The lattice Λ = Φ(Q^{-2}·O_K) ⊂ ℂ^f
    - The norm-one set U ⊂ Λ from Proposition 2.2

    We axiomatize the key properties since the full Minkowski embedding machinery
    requires substantial infrastructure. -/
structure MinkowskiLatticeData (d : AdmissibleDatum) : Type* where
  /-- The Minkowski embedding Φ : K → ℂ^f -/
  phi : d.K → (Fin d.f → ℂ)
  /-- The norm-one set U ⊂ K (from Proposition 2.2) -/
  U : Finset d.K
  /-- Every u ∈ U has complex absolute value 1 under all embeddings -/
  U_norm_one : ∀ u ∈ U, ∀ r : Fin d.f, ‖phi u r‖ = 1
  /-- Every u ∈ U lies in Q^{-2}·O_K -/
  U_integral : letI := d.fieldK; letI := d.charZeroK; letI := d.numberFieldK;
    ∀ u ∈ U, IsIntegral ℤ ((d.Q : d.K) ^ 2 * u)

/-- The sup-norm on ℂ^f: ‖z‖_∞ = max_r |z_r|. -/
noncomputable def supNorm {n : ℕ} [NeZero n] (z : Fin n → ℂ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun r => ‖z r‖)

/-- The sup-norm ball B_R = {z ∈ ℂ^n : ‖z‖_∞ ≤ R} -/
noncomputable def supNormBall {n : ℕ} [NeZero n] (R : ℝ) : Set (Fin n → ℂ) :=
  {z | supNorm z ≤ R}

/-- The lattice Λ = Φ(Q^{-2}·O_K) inside ℂ^f.
    This is the image of the fractional ideal D^{-1}O_K under Φ,
    where D = Q² (Q = product of split primes). -/
noncomputable def minkowskiLattice (d : AdmissibleDatum) (mld : MinkowskiLatticeData d) :
    Set (Fin d.f → ℂ) :=
  letI := d.fieldK; letI := d.charZeroK; letI := d.numberFieldK;
  Set.range (fun x : {x : d.K // IsIntegral ℤ ((d.Q : d.K) ^ 2 * x)} => mld.phi x.val)

/-- For a coset a + Λ, the set X_a = (a + Λ) ∩ B_R.
    Requires NeZero d.f to use the sup-norm. -/
noncomputable def cosetBallIntersection (d : AdmissibleDatum) [NeZero d.f]
    (mld : MinkowskiLatticeData d) (a : Fin d.f → ℂ) (R : ℝ) : Set (Fin d.f → ℂ) :=
  {z | supNorm z ≤ R ∧ ∃ v ∈ minkowskiLattice d mld, z = a + v}

/-- N_a = |X_a| = |{(a + Λ) ∩ B_R}| (coset count).
    We use Set.ncard since X_a may not carry a Fintype instance in general. -/
noncomputable def cosetCount (d : AdmissibleDatum) [NeZero d.f]
    (mld : MinkowskiLatticeData d) (a : Fin d.f → ℂ) (R : ℝ) : ℕ :=
  Set.ncard (cosetBallIntersection d mld a R)

/-- The image of U under Φ, as a subset of the lattice Λ -/
noncomputable def imageU (d : AdmissibleDatum) (mld : MinkowskiLatticeData d) :
    Set (Fin d.f → ℂ) :=
  mld.phi '' (mld.U : Set d.K)

/-- E_a = #{(x,x') ∈ X_a² : x' - x ∈ Φ(U)} (unit-pair count in coset).
    We use Set.ncard for the cardinality of the filtered product set. -/
noncomputable def unitPairCount (d : AdmissibleDatum) [NeZero d.f]
    (mld : MinkowskiLatticeData d) (a : Fin d.f → ℂ) (R : ℝ) : ℕ :=
  let Xa := cosetBallIntersection d mld a R
  Set.ncard {p : (Fin d.f → ℂ) × (Fin d.f → ℂ) |
    p.1 ∈ Xa ∧ p.2 ∈ Xa ∧ p.2 - p.1 ∈ imageU d mld}

/-- b(R) = πR² — the area of one radius-R disc -/
noncomputable def discArea (R : ℝ) : ℝ := Real.pi * R ^ 2

/-- a(R) — the overlap area of two radius-R discs whose centers are distance 1 apart.
    Explicitly: a(R) = 2R² · arccos(1/(2R)) - (1/2)·√(4R²-1)
    for R ≥ 1/2, and 0 for R < 1/2. -/
noncomputable def discOverlapArea (R : ℝ) : ℝ :=
  if R < 1 / 2 then 0
  else 2 * R ^ 2 * Real.arccos (1 / (2 * R)) - (1 / 2) * Real.sqrt (4 * R ^ 2 - 1)

/-- ρ_R = a(R)/b(R) — the disc-overlap ratio -/
noncomputable def discOverlapRatio (R : ℝ) : ℝ :=
  discOverlapArea R / discArea R

/-- Key geometric property: ρ_R = a(R)/b(R) → 1 as R → ∞.
    As R → ∞, two unit-distance discs of radius R overlap in nearly all of their area. -/
axiom discOverlapRatio_tendsto_one :
    Filter.Tendsto discOverlapRatio Filter.atTop (nhds 1)

end UnitDistance
