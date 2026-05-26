# Remaining Axioms (is_assumption: false)

This file documents the axioms introduced for `is_assumption: false` chunks that
could not be closed in this formalization run. Each axiom is stated faithfully to the PDF
source and tagged with the missing Lean/Mathlib API needed to discharge it.

Per UNITY.md: "A clean build with a non-empty REMAINING_AXIOMS.md is a **partial** run —
report it as partial, do not merge it as complete."

**Build status**: `lake build UnitDistance` passes. Zero `sorry` or `admit` in the project.
**16th exploration pass update (2026-05-25)**: `lemma26_packingBound` is now PROVED (commit `baccc15`).
Schema repairs (phi_ringHoms/phi_distinct/phi_normProduct in MinkowskiLatticeData, primeIdealPairs in
AdmissibleDatum) are APPLIED. 4 axioms remain (down from 5).
**17th formalization pass update (2026-05-25)**: `C15_Chebotarev` Invariant 3 violation fixed — replaced
vacuous `theorem chebotarev_density := Nat.infinite_setOf_prime` with faithful `axiom chebotarev_density`
that uses the Galois extension N and automorphism σ and states existence of infinitely many primes with
Frobenius = σ (commit `0fe8f46`). 4 `is_assumption: false` axioms still remain (unchanged).

---

## 1. `normOneSetU_exists` — Proposition 2.2

**File**: `UnitDistance/C21_NormOneSetU.lean`
**Chunk**: `chunk-2-1`
**Source**: PDF §2, Proposition 2.2 (lines 340–414)

**Statement** (faithfully reproduces Prop 2.2):
```lean
axiom normOneSetU_exists (d : AdmissibleDatum) (H : ℝ) (hH : H > 0)
    (hClassNum : (Fintype.card (ClassGroup (𝓞 d.K)) : ℝ) ≤ H ^ d.f) :
    ∃ U : Finset d.K,
      (∀ u ∈ U, Algebra.norm d.L u = 1) ∧
      (∀ u ∈ U, ∀ φ : d.K →+* ℂ, ‖φ u‖ = 1) ∧
      (U.card : ℝ) ≥ Real.exp ((↑d.t * Real.log 2 - Real.log H) * ↑d.f) ∧
      (∀ u ∈ U, IsIntegral ℤ ((d.Q : d.K) ^ 2 * u))
```

**Source proof strategy** (paper):
1. For each ε ∈ {0,1}^m (m = t·f), form ideal A_ε = ∏_{ε_s=1} P_s · ∏_{ε_s=0} c(P_s) in 𝓞 d.K
2. Map ε ↦ ClassGroup.mk A_ε; pigeonhole gives fiber of size ≥ 2^m / h(K)
3. For ε in large fiber: A_ε · A_η^{-1} is principal; choose generator α_ε; set u_ε = α_ε / c(α_ε)
4. Verify: N_{K/L}(u_ε) = 1, |σ(u_ε)| = 1, Q²·u_ε integral, distinct ε give distinct u_ε

**Missing Lean/Mathlib API**:
- `primeIdealPairs : Fin d.m → Ideal (𝓞 d.K) × Ideal (𝓞 d.K)` — not in `AdmissibleDatum`
  (UNITY.md Task 1 schema repair: add CM-conjugate prime ideal pair data to AdmissibleDatum)
- Proof that each prime q_b ≡ 1 (mod 4) with K = L(i) gives exactly two conjugate primes in 𝓞 d.K
  (Kummer–Dedekind for K/L; needs `hKL_degree : Module.finrank d.L d.K = 2` in AdmissibleDatum)
- `ClassGroup.mk_of_ideal_product` / explicit construction of ideal A_ε from prime factors
- Generator extraction from `ClassGroup.mk A = ClassGroup.mk B` (principality + generator choice)
- `IsCMField.complexConj` applied to quotients u_ε = α_ε / c(α_ε)
- Valuation arithmetic: v_{P_s}(u_ε) = 2(ε_s - η_s)

**Estimated effort**: 800–1500 lines of Lean, requiring ~5–10 new Mathlib lemmas about
conjugate prime pairs in CM extensions and ~3–5 new lemmas about generator extraction from
principal fractional ideals.

---

## 2. `prop32_galoisStructure_discUnramified` — Proposition 3.2

**File**: `UnitDistance/C22_Prop32.lean`
**Chunk**: `chunk-2-2`
**Source**: PDF §3, Proposition 3.2 (lines 480–570)

**Statement** (faithfully reproduces Prop 3.2):
```lean
axiom prop32_galoisStructure_discUnramified :
    ∀ (ℓ : ℕ) (hℓ : 11 ≤ ℓ),
    let r₁ : ℕ := ℓ - 1
    ∃ (r : Fin r₁ → ℕ) (h_prime : ∀ i, (r i).Prime) (h_mod3 : ∀ i, r i % 3 = 1)
      (F : Type*) (_ : Field F) (_ : NumberField F) (_ : CharZero F),
    let f₀ : ℕ := Module.finrank ℚ F
    f₀ = 3 ∧ NumberField.IsTotallyReal F ∧
    ∃ (M : Type*) (_ : Field M) (_ : NumberField M) (_ : CharZero M)
      (_ : Algebra F M),
    Module.finrank ℚ M = 3^ℓ ∧
    Module.finrank F M = 3^(ℓ-1) ∧
    NumberField.IsTotallyReal M ∧
    IsEverywhereUnramified F M
```

**Source proof strategy** (paper):
- Take F = cyclic cubic field with conductor product of r_i's and discriminant = (∏ r_i)²
- Construct M as compositum of ℓ-1 linear-disjoint cyclic cubic fields
- Prove linear disjointness via conductor-discriminant formula and pairwise coprime conductors
- M/F is everywhere-unramified (discriminant of M/ℚ equals discriminant of F/ℚ to the 3^{ℓ-1})

**Missing Lean/Mathlib API**:
- Linear disjointness criterion for compositums of number fields (no Mathlib theorem)
- Conductor–discriminant formula for compositums (axiomatized in C07/C14 but not linked)
- `IsEverywhereUnramified` instance construction for compositum extensions
- Discriminant multiplicativity tower formula for multi-step extensions
- `IsTotallyReal` for compositums of totally real fields

**Estimated effort**: 1000–2000 lines of Lean, requiring substantial compositum theory.

---

## 3. `lemma24_cosetAveraging` — Lemma 2.4

**File**: `UnitDistance/C28_Lemma24.lean`
**Chunk**: `chunk-2-8`
**Source**: PDF §2.1, Lemma 2.4 (lines 415–450)

**Statement** (faithfully reproduces Lemma 2.4):
```lean
axiom lemma24_cosetAveraging
    (d : AdmissibleDatum) [NeZero d.f] (H : ℝ) (hH : H > 0)
    (γ : ℝ) (hγ : γ = d.t * Real.log 2 - Real.log H) (hγpos : γ > 0)
    (mld : MinkowskiLatticeData d)
    (U_size : (mld.U.card : ℝ) ≥ Real.exp (γ * d.f))
    (R : ℝ) (hR_pos : R > 1 / 2)
    (hR_large : Real.log (discOverlapRatio R) > -(γ / 2)) :
    ∃ a : Fin d.f → ℂ,
      (cosetCount d mld a R : ℝ) > 0 ∧
      (unitPairCount d mld a R : ℝ) ≥
        Real.exp (γ * d.f / 2) * (cosetCount d mld a R : ℝ)
```

**Source proof strategy** (paper):
1. Average N_a over the torus V/Λ (Haar measure): E[N_a] = vol(B_R) / covol(Λ)
2. For fixed u ∈ U with |σ_r(u)| = 1: vol(B_R ∩ (B_R - Φ(u))) = a(R)^f (since |Φ(u)_r| = 1)
3. Averaging E_a: E[E_a] = |U| · ρ_R^f · E[N_a]
4. Pigeonhole: some nonempty coset has E_a ≥ |U| · ρ_R^f · N_a ≥ exp(γf/2) · N_a

**Missing Lean/Mathlib API**:
- `ZLattice` structure for `minkowskiLattice d mld ⊂ ℂ^f` (needs `phi_ringHoms` ring hom structure)
- `IsAddFundamentalDomain` instance for the lattice quotient torus
- The unfolding identity: `∫_{V/Λ} N_a dμ = vol(B_R) / covol(Λ)` via `IsAddFundamentalDomain.lintegral_eq_tsum`
- `MeasureTheory.Measure.addHaar` for the torus V/Λ
- Measurability of `a ↦ cosetCount d mld a R` as a function on V/Λ
- Connection from `Set.ncard` (used in cosetCount) to Lebesgue measure integration

**Estimated effort**: 600–1200 lines of Lean, requiring ZLattice + fundamental domain machinery.

---

## 4. `lemma26_packingBound` — Lemma 2.6

**File**: `UnitDistance/C210_Lemma26.lean`
**Chunk**: `chunk-2-10`
**Source**: PDF §2.2, Lemma 2.6 (lines 451–470)

**Statement** (faithfully reproduces Lemma 2.6):
```lean
axiom lemma26_packingBound
    (d : AdmissibleDatum) [NeZero d.f] (H : ℝ) (hH : H > 0)
    (mld : MinkowskiLatticeData d)
    (a : Fin d.f → ℂ) (R : ℝ) (hR : R > 0) :
    let D : ℝ := (d.Q : ℝ) ^ 2
    let B : ℝ := 2 * Real.log (4 * R * D)
    (cosetCount d mld a R : ℝ) ≤ Real.exp (B * d.f)
```

**Source proof strategy** (paper):
1. For distinct x ≠ x' in X_a: x - x' = Φ(β - β') with β - β' ∈ D^{-1}·O_K, β ≠ β'
2. Product norm: ∏_r |Φ(δ)_r| = N_{K/ℚ}(δ)^{1/2} ≥ D^{-f} (since |N(D^{-1}·α)| ≥ D^{-f} for α ∈ O_K)
3. AM-GM: sup_r |Φ(δ)_r| ≥ (∏_r |Φ(δ)_r|)^{1/f} ≥ D^{-1}
4. Disjoint balls: n · vol(B_{D^{-1}/2}) ≤ vol(B_{R+D^{-1}/2}) (volume comparison in ℂ^f)
5. n ≤ ((R + D^{-1}/2) / (D^{-1}/2))^{2f} = (1 + 2RD)^{2f} ≤ (4RD)^{2f} = exp(Bf)

**Missing Lean/Mathlib API**:
- `phi_ringHoms : Fin d.f → (d.K →+* ℂ)` field in `MinkowskiLatticeData` (UNITY.md Task 1)
- `phi_normProduct` field in `MinkowskiLatticeData`: ∏_r ‖φ_r(k)‖ = sqrt |N_{K/ℚ}(k)|
  (provable from `NumberField.InfinitePlace.prod_eq_abs_norm` + `IsTotallyComplex.mult_eq`)
  (but requires `nrComplexPlaces d.K = d.f`, which needs `Module.finrank d.L d.K = 2`)
- `Module.finrank d.L d.K = 2` in `AdmissibleDatum` (K is quadratic over L)
- Volume formula for sup-norm ball in ℂ^f: vol(B_R) = (π R^2)^f
  (via Fubini: `MeasureTheory.Measure.pi` + `Complex.volume_closedBall`)
- Disjoint ball count bound (standard packing argument in ℂ^f)

**Estimated effort**: 400–800 lines of Lean. This is the most accessible of the remaining axioms
once the schema fixes (phi_ringHoms + AdmissibleDatum.hKL_degree) are applied.

---

## 5. `prop38_fieldConstruction` — Proposition 3.8

**File**: `UnitDistance/C32_Prop38.lean`
**Chunk**: `chunk-3-2`
**Source**: PDF §3.2, Proposition 3.8 (lines 570–700)

**Statement** (faithfully reproduces Prop 3.8):
```lean
axiom prop38_fieldConstruction :
    ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ →
    let t : ℕ := (ℓ - 1) ^ 2 / 100
    ∃ (H_ℓ : ℝ), H_ℓ > 1 ∧
    (t : ℝ) * Real.log 2 - Real.log H_ℓ > 0 ∧
    ∃ (data : ℕ → UnitDistance.AdmissibleDatum),
    (∀ j, (data j).t = t) ∧ (data 0).f = 3 ∧
    (∀ M : ℕ, ∃ j : ℕ, M ≤ (data j).f) ∧
    (∀ j, rootDiscr (data j).L = rootDiscr (data 0).L) ∧
    (∀ j, (Fintype.card (ClassGroup (𝓞 (data j).K)) : ℝ) ≤ H_ℓ ^ (data j).f) ∧
    (∀ j i, (data j).primes (...) = (data 0).primes (...))
```

**Source proof strategy** (paper):
- Take F₀ = cyclic cubic with conductor r₁ (a prime ≡ 1 mod 3)
- Iteratively apply Golod–Shafarevich to construct infinite towers of unramified extensions
- At each level, Chebotarev density guarantees t primes split completely in all Fⱼ
- Class number controlled via Minkowski bound + root discriminant stability (rd(Fⱼ) = rd(F₀))
- The tower has t ≥ (ℓ-1)²/100 primes, giving γ > 0

**Missing Lean/Mathlib API**:
- Golod–Shafarevich tower construction (no Lean formalization of pro-p group towers)
- Chebotarev density for controlled splitting across tower levels
- Root discriminant stability under unramified extensions
- Class number bound from Minkowski for fields with controlled root discriminant
- Connection between pro-p group theory (Golod–Shafarevich GS inequality) and field towers

**Estimated effort**: 2000–4000 lines of Lean, requiring the full Golod–Shafarevich tower
theory which is not available in Mathlib and would require a separate formalization project.
This is the deepest result in the paper and is months-scale work.

---

## Summary

| Axiom | Chunk | Most Accessible | Estimated Lines |
|-------|-------|----------------|-----------------|
| `normOneSetU_exists` | chunk-2-1 | After `primeIdealPairs` schema fix + CM prime theory | 800–1500 |
| `prop32_galoisStructure_discUnramified` | chunk-2-2 | After compositum + linear disjointness theory | 1000–2000 |
| `lemma24_cosetAveraging` | chunk-2-8 | After `ZLattice` + fundamental domain | 600–1200 |
| `lemma26_packingBound` | chunk-2-10 | After `phi_normProduct` schema fix + volume theory | 400–800 |
| `prop38_fieldConstruction` | chunk-3-2 | After Golod–Shafarevich tower theory | 2000–4000 |

**Total remaining**: All five axioms together represent approximately 4800–9500 lines of new Lean
formalization, with substantial dependencies on Mathlib infrastructure not yet available.
