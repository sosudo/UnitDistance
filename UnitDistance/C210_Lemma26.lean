import Mathlib
import UnitDistance.C02_AdmissibleDatum
import UnitDistance.C03_BasicFieldConventions
import UnitDistance.C20_MinkowskiLattice
import UnitDistance.C29_Lemma25

set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace UnitDistance

open Real NumberField MeasureTheory

-- ============================================================
-- Helper: finrank ℚ K = 2 * d.f for CM field K
-- ============================================================

private lemma admissibleDatum_finrank_K (d : AdmissibleDatum) :
    letI := d.fieldK; letI := d.numberFieldK; letI := d.cmFieldK
    Module.finrank ℚ d.K = 2 * d.f := by
  letI := d.fieldK; letI := d.numberFieldK; letI := d.cmFieldK
  rw [IsTotallyComplex.finrank]
  -- Goal: 2 * InfinitePlace.nrComplexPlaces d.K = 2 * d.f
  congr 1
  -- Goal: InfinitePlace.nrComplexPlaces d.K = d.f
  rw [show InfinitePlace.nrComplexPlaces d.K =
      Fintype.card (InfinitePlace d.K) from ?_, d.hKL_card']
  · -- InfinitePlace.nrComplexPlaces d.K = Fintype.card (InfinitePlace d.K)
    -- Since K is totally complex, InfinitePlace.nrRealPlaces K = 0
    have : InfinitePlace.nrRealPlaces d.K = 0 := IsTotallyComplex.nrRealPlaces_eq_zero d.K
    linarith [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := d.K)]

-- ============================================================
-- Helper: supNorm basic properties
-- ============================================================

private lemma supNorm_coord_le {n : ℕ} [NeZero n] (z : Fin n → ℂ) (r : Fin n) :
    ‖z r‖ ≤ supNorm z :=
  Finset.le_sup' (fun r => ‖z r‖) (Finset.mem_univ r)

private lemma supNorm_sub {n : ℕ} [NeZero n] (x y : Fin n → ℂ) :
    supNorm (x - y) ≤ supNorm x + supNorm y := by
  unfold supNorm
  apply Finset.sup'_le
  intro r _
  calc ‖(x - y) r‖ = ‖x r - y r‖ := by simp [Pi.sub_apply]
    _ ≤ ‖x r‖ + ‖y r‖ := norm_sub_le _ _
    _ ≤ Finset.sup' Finset.univ Finset.univ_nonempty (fun r => ‖x r‖) +
        Finset.sup' Finset.univ Finset.univ_nonempty (fun r => ‖y r‖) :=
        add_le_add (Finset.le_sup' (fun r => ‖x r‖) (Finset.mem_univ r))
                   (Finset.le_sup' (fun r => ‖y r‖) (Finset.mem_univ r))

-- ============================================================
-- Helper: norm lower bound for nonzero integral elements
-- ============================================================

/-- For nonzero γ ∈ D^{-1}·O_K (i.e., Q²γ integral, γ ≠ 0),
    the product of norms ≥ D^{-f}. -/
private lemma phi_normProduct_lower_bound (d : AdmissibleDatum) [NeZero d.f]
    (mld : MinkowskiLatticeData d)
    (γ : d.K)
    (hγ_int : letI := d.fieldK; letI := d.charZeroK; letI := d.numberFieldK;
              IsIntegral ℤ ((d.Q : d.K) ^ 2 * γ))
    (hγ_ne : letI := d.fieldK; γ ≠ 0) :
    (d.Q : ℝ) ^ (-(2 * (d.f : ℤ))) ≤ ∏ r : Fin d.f, ‖mld.phi_ringHoms r γ‖ := by
  letI := d.fieldK; letI := d.charZeroK; letI := d.numberFieldK; letI := d.cmFieldK
  have hprod := mld.phi_normProduct γ hγ_ne
  rw [hprod]
  have hQ_pos : (0 : ℝ) < (d.Q : ℝ) :=
    by exact_mod_cast Finset.one_le_prod' (fun i _ => (d.primePrime i).one_le)
  -- Get δ = Q²γ ∈ 𝓞 K, δ ≠ 0
  have hQ2_ne : (d.Q : d.K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
      (Finset.one_le_prod' (fun i _ => (d.primePrime i).one_le)))
  have hQ2γ_ne : (d.Q : d.K) ^ 2 * γ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hQ2_ne) hγ_ne
  let δ : 𝓞 d.K := ⟨(d.Q : d.K) ^ 2 * γ, hγ_int⟩
  have hδ_ne : δ ≠ 0 := fun h => hQ2γ_ne (congrArg RingOfIntegers.val h)
  -- |Algebra.norm ℤ δ| ≥ 1
  have hintNorm_ge1 : (1 : ℤ) ≤ |(Algebra.norm ℤ δ)| :=
    Int.one_le_abs (by rwa [ne_eq, Algebra.norm_eq_zero_iff])
  -- |Algebra.norm ℚ (δ : K)| ≥ 1
  have h_norm_ge1 : (1 : ℝ) ≤ |(Algebra.norm ℚ (δ : d.K) : ℝ)| := by
    have h1 : (1 : ℝ) ≤ |(Algebra.norm ℤ δ : ℤ)| := by exact_mod_cast hintNorm_ge1
    calc (1 : ℝ) ≤ |(Algebra.norm ℤ δ : ℤ)| := h1
      _ = |(Algebra.norm ℚ (δ : d.K) : ℝ)| := by
          congr 1; rw [← Algebra.coe_norm_int δ]; push_cast; rfl
  -- Compute norm of δ: Algebra.norm ℚ (Q²γ) = Q^{2f} * norm ℚ γ
  have h_finrank : Module.finrank ℚ d.K = 2 * d.f := admissibleDatum_finrank_K d
  have h_norm_expand : Algebra.norm ℚ (δ : d.K) =
      (d.Q : ℚ) ^ (2 * Module.finrank ℚ d.K) * Algebra.norm ℚ γ := by
    show Algebra.norm ℚ ((d.Q : d.K) ^ 2 * γ) =
        (d.Q : ℚ) ^ (2 * Module.finrank ℚ d.K) * Algebra.norm ℚ γ
    rw [map_mul (Algebra.norm ℚ)]
    have hQK : (d.Q : d.K) = algebraMap ℚ d.K (d.Q : ℚ) := by push_cast; simp
    rw [hQK, map_pow, Algebra.norm_algebraMap]
    ring
  -- |norm (Q²γ)| = Q^{4f} * |norm γ|
  have h_abs_expand : |(Algebra.norm ℚ (δ : d.K) : ℝ)| =
      (d.Q : ℝ) ^ (4 * d.f) * |(Algebra.norm ℚ γ : ℝ)| := by
    rw [h_norm_expand]
    push_cast
    rw [abs_mul, abs_pow, abs_of_nonneg (by positivity), h_finrank]
    push_cast; ring_nf
  -- 1 ≤ Q^{4f} * |norm γ|
  have h_lower : (1 : ℝ) ≤ (d.Q : ℝ) ^ (4 * d.f) * |(Algebra.norm ℚ γ : ℝ)| := by
    rw [← h_abs_expand]; exact h_norm_ge1
  -- Goal: Q^{-2f} ≤ |norm γ|^(1/2)
  -- i.e., (Q^{2f})⁻¹ ≤ |norm γ|^(1/2)
  -- i.e., 1 ≤ |norm γ|^(1/2) * Q^{2f}
  -- Proof: (|norm γ|^(1/2) * Q^{2f})^2 = |norm γ| * Q^{4f} ≥ 1
  have hQf_pos : (0 : ℝ) < (d.Q : ℝ) ^ (2 * d.f) := pow_pos hQ_pos _
  -- Convert Q^(-(2f:ℤ)) to (Q^(2f))⁻¹ then use inv_le
  rw [show (d.Q : ℝ) ^ (-(2 * (d.f : ℤ))) = ((d.Q : ℝ)^(2*d.f))⁻¹ from by
    rw [zpow_neg]; norm_cast]
  rw [inv_le_iff_one_le_mul₀' hQf_pos]
  -- Goal: 1 ≤ |norm γ|^(1/2) * Q^{2f}
  -- Use h_lower : 1 ≤ Q^{4f} * |norm γ| to derive the goal by squaring argument
  -- After inv_le_iff_one_le_mul₀', goal is: 1 ≤ ↑|(Algebra.norm ℚ) γ|^(1/2) * Q^(2f)
  -- where ↑|(Algebra.norm ℚ) γ| means (↑(|(Algebra.norm ℚ) γ| : ℚ) : ℝ)
  -- and h_lower uses |↑((Algebra.norm ℚ) γ)| = |(↑(Algebra.norm ℚ γ) : ℝ)|
  -- These are equal: |↑q| = ↑|q| for q : ℚ
  have habs_eq : ↑|(Algebra.norm ℚ) γ| = |(Algebra.norm ℚ γ : ℝ)| := by norm_cast
  rw [habs_eq]
  have habsnn : (0 : ℝ) ≤ |(Algebra.norm ℚ γ : ℝ)| := abs_nonneg _
  have hlhs_nn : 0 ≤ |(Algebra.norm ℚ γ : ℝ)| ^ ((1:ℝ)/2) * (d.Q : ℝ) ^ (2 * d.f) :=
    mul_nonneg (Real.rpow_nonneg habsnn _) hQf_pos.le
  have h_sq : 1 ≤ (|(Algebra.norm ℚ γ : ℝ)| ^ ((1:ℝ)/2) * (d.Q : ℝ) ^ (2 * d.f)) ^ 2 := by
    have hx2 : (|(Algebra.norm ℚ γ : ℝ)| ^ ((1:ℝ)/2)) ^ 2 = |(Algebra.norm ℚ γ : ℝ)| := by
      rw [← Real.rpow_natCast (|(Algebra.norm ℚ γ : ℝ)|^_) 2, ← Real.rpow_mul habsnn]; norm_num
    rw [mul_pow, hx2, ← pow_mul, show 2 * d.f * 2 = 4 * d.f from by ring]
    linarith [mul_comm ((d.Q : ℝ) ^ (4 * d.f)) (|(Algebra.norm ℚ γ : ℝ)|)]
  nlinarith [sq_nonneg (|(Algebra.norm ℚ γ : ℝ)| ^ ((1:ℝ)/2) * (d.Q : ℝ) ^ (2 * d.f) - 1),
             hlhs_nn]

-- ============================================================
-- Helper: sup-norm separation of lattice differences
-- ============================================================

/-- For distinct x, x' ∈ cosetBallIntersection, supNorm(x - x') ≥ D^{-1} -/
private lemma cosetBall_separated (d : AdmissibleDatum) [NeZero d.f]
    (mld : MinkowskiLatticeData d)
    (a : Fin d.f → ℂ) (R : ℝ)
    (x x' : Fin d.f → ℂ)
    (hx : x ∈ cosetBallIntersection d mld a R)
    (hx' : x' ∈ cosetBallIntersection d mld a R)
    (hne : x ≠ x') :
    (d.Q : ℝ)^(-(2:ℤ)) ≤ supNorm (x - x') := by
  letI := d.fieldK; letI := d.charZeroK; letI := d.numberFieldK; letI := d.cmFieldK
  -- Get β, β' with x = a + phi β, x' = a + phi β'
  obtain ⟨_, v, hv_mem, rfl⟩ := hx
  obtain ⟨_, v', hv'_mem, rfl⟩ := hx'
  simp only [minkowskiLattice, Set.mem_range] at hv_mem hv'_mem
  obtain ⟨⟨β, hβ_int⟩, rfl⟩ := hv_mem
  obtain ⟨⟨β', hβ'_int⟩, rfl⟩ := hv'_mem
  -- x ≠ x' means a + phi β ≠ a + phi β', i.e., phi β ≠ phi β', i.e., β ≠ β'
  have hβ_ne : β ≠ β' := by
    intro heq
    apply hne
    simp [heq]
  -- Let γ = β - β', which is nonzero
  let γ := β - β'
  have hγ_ne : γ ≠ 0 := sub_ne_zero.mpr hβ_ne
  -- γ ∈ D^{-1}·O_K: Q²γ = Q²β - Q²β' is integral
  have hγ_int : IsIntegral ℤ ((d.Q : d.K) ^ 2 * γ) := by
    have : (d.Q : d.K) ^ 2 * γ = (d.Q : d.K) ^ 2 * β - (d.Q : d.K) ^ 2 * β' := by
      ring
    rw [this]
    exact hβ_int.sub hβ'_int
  -- supNorm(x - x') = supNorm(phi β - phi β') = supNorm(phi γ)
  have hphi_eq : ∀ r, mld.phi γ r = mld.phi_ringHoms r γ := fun r => mld.phi_eq γ r
  have hphi_sub : ∀ r, mld.phi γ r = mld.phi β r - mld.phi β' r := by
    intro r
    rw [hphi_eq r, mld.phi_eq β r, mld.phi_eq β' r]
    letI := d.fieldK
    exact (mld.phi_ringHoms r).map_sub β β'
  have hx_diff : (a + mld.phi β) - (a + mld.phi β') = mld.phi γ := by
    ext r; simp only [Pi.sub_apply, Pi.add_apply]
    rw [hphi_sub r]; ring
  rw [hx_diff]
  -- supNorm(phi γ) = max_r ‖phi γ r‖ = max_r ‖phi_ringHoms r γ‖
  have h_supnorm_eq : supNorm (mld.phi γ) =
      Finset.sup' Finset.univ Finset.univ_nonempty (fun r => ‖mld.phi_ringHoms r γ‖) := by
    unfold supNorm
    congr 1; ext r; exact congrArg norm (hphi_eq r)
  rw [h_supnorm_eq]
  -- supNorm ≥ (∏_r ‖phi_ringHoms r γ‖)^{1/f} ≥ (D^{-f})^{1/f} = D^{-1}
  -- by AM-GM: Finset.sup' ≥ (Finset.prod / card)^{1/...}
  -- Actually: max ≥ (∏)^{1/f} by AM-GM (geometric mean ≤ max)
  -- i.e., ∏ aᵢ ≤ (max aᵢ)^f, so (∏ aᵢ)^{1/f} ≤ max aᵢ
  have hf_pos : (0 : ℝ) < d.f := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d.f))
  have h_prod_lower := phi_normProduct_lower_bound d mld γ hγ_int hγ_ne
  -- max ≥ (∏ ‖φ_r γ‖)^(1/f) ≥ (D^{-f})^(1/f) = D^{-1}
  -- Step 1: max^f ≥ ∏ ‖φ_r γ‖
  have h_max_ge_prod :
      (Finset.sup' Finset.univ Finset.univ_nonempty (fun r => ‖mld.phi_ringHoms r γ‖)) ^ d.f ≥
      ∏ r : Fin d.f, ‖mld.phi_ringHoms r γ‖ := by
    show ∏ r : Fin d.f, ‖mld.phi_ringHoms r γ‖ ≤
        (Finset.sup' Finset.univ Finset.univ_nonempty (fun r => ‖mld.phi_ringHoms r γ‖)) ^ d.f
    have key : ∏ r : Fin d.f, ‖mld.phi_ringHoms r γ‖ ≤
        ∏ _ : Fin d.f, Finset.sup' Finset.univ Finset.univ_nonempty (fun r => ‖mld.phi_ringHoms r γ‖) :=
      Finset.prod_le_prod (fun r _ => norm_nonneg _)
        (fun r _ => Finset.le_sup' (fun r => ‖mld.phi_ringHoms r γ‖) (Finset.mem_univ r))
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at key
    exact key
  -- Step 2: (D^{-f})^(1/f) = D^{-1}
  have hD_pos : (0 : ℝ) < (d.Q : ℝ) ^ 2 :=
    pow_pos (by exact_mod_cast Finset.one_le_prod' (fun i _ => (d.primePrime i).one_le)) 2
  -- We need: D^{-1} ≤ max
  -- D^{-1} = (D^{-f})^{1/f} ≤ (∏ ‖φ_r γ‖)^{1/f} ≤ max (using monotone rpow and max ≥ (prod/max^{f-1}))
  -- Cleaner: max ≥ (∏ ‖φ_r γ‖)^{1/f} ≥ (D^{-f})^{1/f} = D^{-1}
  have h_max_pos : 0 ≤ Finset.sup' Finset.univ Finset.univ_nonempty (fun r => ‖mld.phi_ringHoms r γ‖) := by
    obtain ⟨r, _⟩ := Finset.univ_nonempty (α := Fin d.f)
    exact le_trans (norm_nonneg _) (Finset.le_sup' (fun r => ‖mld.phi_ringHoms r γ‖) (Finset.mem_univ r))
  -- Use: M^f ≥ P implies M ≥ P^{1/f} (for M ≥ 0, P ≥ 0, f > 0)
  set M := Finset.sup' Finset.univ Finset.univ_nonempty (fun r => ‖mld.phi_ringHoms r γ‖)
  -- Goal: Q^{-2} ≤ M
  -- We have: M^f ≥ ∏ ‖φ_r γ‖ ≥ Q^{-2f}, so (M * Q^2)^f ≥ 1, hence M * Q^2 ≥ 1, i.e. M ≥ Q^{-2}
  have hQ2_pos : (0 : ℝ) < (d.Q : ℝ) ^ 2 := hD_pos
  have h_Mf_ge : (d.Q : ℝ) ^ (-(2 * (d.f : ℤ))) ≤ M ^ d.f := by
    calc (d.Q : ℝ) ^ (-(2 * (d.f : ℤ))) ≤ ∏ r : Fin d.f, ‖mld.phi_ringHoms r γ‖ := h_prod_lower
      _ ≤ M ^ d.f := h_max_ge_prod
  have hMQ2_f : 1 ≤ (M * (d.Q : ℝ)^2) ^ d.f := by
    rw [mul_pow]
    calc (1 : ℝ) ≤ (d.Q : ℝ) ^ (-(2 * (d.f : ℤ))) * ((d.Q : ℝ) ^ 2) ^ d.f := by
          have hQ_pos2 : (0 : ℝ) < (d.Q : ℝ) :=
            by exact_mod_cast Finset.one_le_prod' (fun i _ => (d.primePrime i).one_le)
          have : (d.Q : ℝ) ^ (-(2 * (d.f : ℤ))) = ((d.Q : ℝ)^(2*d.f))⁻¹ := by
            rw [zpow_neg]; norm_cast
          rw [this, ← pow_mul, inv_mul_cancel₀ (pow_pos hQ_pos2 _).ne']
        _ ≤ M ^ d.f * ((d.Q : ℝ) ^ 2) ^ d.f :=
            mul_le_mul_of_nonneg_right h_Mf_ge
              (pow_nonneg (pow_nonneg (by positivity) 2) d.f)
  -- (M * Q^2)^f ≥ 1 implies M * Q^2 ≥ 1 (since f > 0 and M * Q^2 ≥ 0)
  have hMQ2_nn : 0 ≤ M * (d.Q : ℝ) ^ 2 := mul_nonneg h_max_pos hQ2_pos.le
  have hMQ2_ge1 : 1 ≤ M * (d.Q : ℝ) ^ 2 :=
    (one_le_pow_iff_of_nonneg hMQ2_nn (Nat.pos_of_ne_zero (NeZero.ne d.f)).ne').mp hMQ2_f
  -- Conclude: Q^{-2} ≤ M
  rw [zpow_neg, zpow_ofNat]
  have hQ2 : (0 : ℝ) < (d.Q : ℝ) ^ 2 := hQ2_pos
  have : (d.Q : ℝ) ^ 2 * ((d.Q : ℝ) ^ 2)⁻¹ ≤ (d.Q : ℝ) ^ 2 * M := by
    rw [mul_inv_cancel₀ hQ2.ne']
    linarith [mul_comm M ((d.Q : ℝ) ^ 2)]
  exact le_of_mul_le_mul_left this hQ2

-- ============================================================
-- Helpers for packing bound (measure-theoretic)
-- ============================================================

/-- finrank ℝ (Fin f → ℂ) = 2 * f -/
private lemma finrank_fin_complex (f : ℕ) [NeZero f] :
    Module.finrank ℝ (Fin f → ℂ) = 2 * f := by
  rw [Module.finrank_pi_fintype ℝ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Complex.finrank_real_complex]; ring

/-- supNorm = ‖·‖ on Fin f → ℂ -/
private lemma supNorm_eq_norm {f : ℕ} [NeZero f] (z : Fin f → ℂ) :
    supNorm z = ‖z‖ := by
  unfold supNorm
  apply le_antisymm
  · apply Finset.sup'_le; intro i _; exact norm_le_pi_norm z i
  · have hnn : 0 ≤ Finset.sup' Finset.univ Finset.univ_nonempty (fun r => ‖z r‖) := by
      obtain ⟨j, hj⟩ := Finset.univ_nonempty (α := Fin f)
      exact le_trans (norm_nonneg (z j)) (Finset.le_sup' (fun r => ‖z r‖) hj)
    exact (pi_norm_le_iff_of_nonneg hnn).mpr
      (fun i => Finset.le_sup' (fun r => ‖z r‖) (Finset.mem_univ i))

/-- Packing bound via Haar measure: a δ-separated set in the L² ball of radius R
    in ℂ^f has at most (2R/δ + 1)^{2f} elements. -/
private lemma packing_bound_fin (f : ℕ) [NeZero f]
    (S : Finset (Fin f → ℂ))
    (R δ : ℝ) (hδ : 0 < δ) (hR : 0 < R)
    (hS_ball : ∀ s ∈ S, ‖s‖ ≤ R)
    (hS_sep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → δ ≤ ‖s - t‖) :
    (S.card : ℝ) ≤ (2 * R / δ + 1) ^ (2 * f) := by
  set μ := (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (Fin f → ℂ))
  have hδ' : 0 < δ / 2 := by positivity
  have hRδ' : 0 < R + δ / 2 := by positivity
  have hDisj : (S : Set (Fin f → ℂ)).PairwiseDisjoint
      (fun s => Metric.ball s (δ/2)) := by
    intro s hs t ht hst
    apply Set.disjoint_left.mpr
    intro z hzs hzt
    rw [Metric.mem_ball] at hzs hzt
    have hsep := hS_sep s hs t ht hst
    have htri : ‖s - t‖ ≤ ‖z - s‖ + ‖z - t‖ := by
      calc ‖s - t‖ = ‖(s - z) + (z - t)‖ := by ring_nf
        _ ≤ ‖s - z‖ + ‖z - t‖ := norm_add_le _ _
        _ = ‖z - s‖ + ‖z - t‖ := by rw [norm_sub_rev]
    linarith [show ‖z - s‖ < δ/2 from by rwa [dist_eq_norm] at hzs,
              show ‖z - t‖ < δ/2 from by rwa [dist_eq_norm] at hzt]
  have hBall_sub : ∀ s ∈ S, Metric.ball s (δ/2) ⊆
      Metric.ball (0 : Fin f → ℂ) (R + δ/2) := by
    intro s hs z hz
    rw [Metric.mem_ball, dist_zero_right]; rw [Metric.mem_ball] at hz
    have hzs : ‖z - s‖ < δ/2 := by rwa [dist_eq_norm] at hz
    calc ‖z‖ = ‖(z - s) + s‖ := by ring_nf
      _ ≤ ‖z - s‖ + ‖s‖ := norm_add_le _ _
      _ < δ/2 + R := add_lt_add_of_lt_of_le hzs (hS_ball s hs)
      _ = R + δ/2 := add_comm _ _
  have hvol : ∀ (x : Fin f → ℂ) (r : ℝ) (hr : 0 ≤ r),
      μ (Metric.ball x r) = ENNReal.ofReal (r ^ (2*f)) * μ (Metric.ball 0 1) := by
    intro x r hr
    have := MeasureTheory.Measure.addHaar_ball μ x hr
    rwa [finrank_fin_complex] at this
  have h_unit_pos : 0 < μ (Metric.ball (0 : Fin f → ℂ) 1) :=
    Metric.measure_ball_pos μ 0 (by norm_num)
  have h_unit_fin : μ (Metric.ball (0 : Fin f → ℂ) 1) < ⊤ :=
    MeasureTheory.measure_ball_lt_top
  have hpack_μ : (S.card : ENNReal) * μ (Metric.ball (0 : Fin f → ℂ) (δ/2)) ≤
      μ (Metric.ball 0 (R + δ/2)) := by
    rw [show (S.card : ENNReal) = ∑ _s ∈ S, (1 : ENNReal) by simp]
    rw [Finset.sum_mul]
    rw [show ∑ _s ∈ S, (1 : ENNReal) * μ (Metric.ball 0 (δ/2)) =
        ∑ s ∈ S, μ (Metric.ball s (δ/2)) from
      Finset.sum_congr rfl (fun s _ => by
        rw [one_mul, hvol s _ hδ'.le, hvol 0 _ hδ'.le])]
    rw [← MeasureTheory.measure_biUnion_finset hDisj
        (fun _ _ => measurableSet_ball)]
    exact μ.mono (fun z hz => by
      simp only [Set.mem_iUnion] at hz
      obtain ⟨s, hs, hz⟩ := hz
      exact hBall_sub s hs hz)
  rw [hvol 0 _ hδ'.le, hvol 0 _ hRδ'.le] at hpack_μ
  have hpack_enn : (S.card : ENNReal) * ENNReal.ofReal ((δ/2) ^ (2*f)) ≤
      ENNReal.ofReal ((R + δ/2) ^ (2*f)) := by
    have h1 : (S.card : ENNReal) * ENNReal.ofReal ((δ/2) ^ (2*f)) * μ (Metric.ball 0 1) ≤
              ENNReal.ofReal ((R + δ/2) ^ (2*f)) * μ (Metric.ball 0 1) := by
      calc (S.card : ENNReal) * ENNReal.ofReal ((δ/2) ^ (2*f)) * μ (Metric.ball 0 1)
          = (S.card : ENNReal) * (ENNReal.ofReal ((δ/2) ^ (2*f)) * μ (Metric.ball 0 1)) := by ring
        _ ≤ ENNReal.ofReal ((R + δ/2) ^ (2*f)) * μ (Metric.ball 0 1) := hpack_μ
    exact (ENNReal.mul_le_mul_iff_left h_unit_pos.ne' h_unit_fin.ne).mp h1
  have h_real : (S.card : ℝ) * (δ/2) ^ (2*f) ≤ (R + δ/2) ^ (2*f) := by
    have := ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top |>.mpr hpack_enn
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal (pow_nonneg hδ'.le _),
        ENNReal.toReal_ofReal (pow_nonneg hRδ'.le _)] at this
    exact this
  calc (S.card : ℝ) ≤ (R + δ/2) ^ (2*f) / (δ/2) ^ (2*f) :=
        by rwa [le_div_iff₀ (pow_pos hδ' _)]
    _ = ((R + δ/2) / (δ/2)) ^ (2*f) := (div_pow _ _ _).symm
    _ = (2 * R / δ + 1) ^ (2*f) := by congr 1; field_simp

-- ============================================================
-- Helper: cardinality bound from injection into Finset
-- ============================================================

/-- Lemma 2.6 (Packing bound): cosetCount d mld a R ≤ exp(B · f),
    where B = 2 · log(4RD), D = Q² = (∏ qᵢ)². -/
theorem lemma26_packingBound
    (d : AdmissibleDatum) [NeZero d.f]
    (mld : MinkowskiLatticeData d)
    (γ R : ℝ) (hR : R > 1 / 2) (hγpos : γ > 0)
    (a : Fin d.f → ℂ)
    (hcoset_nonempty : (cosetCount d mld a R : ℝ) > 0)
    (hcoset_good : (unitPairCount d mld a R : ℝ) ≥
                    Real.exp (γ * d.f / 2) * cosetCount d mld a R) :
    let D := (d.Q : ℝ) ^ 2
    let B := 2 * Real.log (4 * R * D)
    let n := cosetCount d mld a R
    (n : ℝ) ≤ Real.exp (B * d.f) := by
  intro D B n
  -- -------------------------
  -- Setup
  -- -------------------------
  let X := cosetBallIntersection d mld a R
  have hX_fin : X.Finite := by
    have hpos : 0 < cosetCount d mld a R := by exact_mod_cast hcoset_nonempty
    exact Set.finite_of_ncard_pos hpos
  -- n = Set.ncard X
  have hn_eq : n = Set.ncard X := rfl
  -- D = Q^2
  have hD_def : D = (d.Q : ℝ) ^ 2 := rfl
  -- Q ≥ 1
  have hQ_ge1 : (1 : ℕ) ≤ d.Q :=
    Finset.one_le_prod' (fun i _ => (d.primePrime i).one_le)
  have hQ_pos : (0 : ℝ) < (d.Q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  -- D ≥ 1
  have hD_ge1 : (1 : ℝ) ≤ D := by
    rw [hD_def]
    exact one_le_pow₀ (by exact_mod_cast hQ_ge1)
  -- B = 2 * log(4RD)
  -- 4RD ≥ 2 since R > 1/2 and D ≥ 1
  have h4RD_ge2 : 4 * R * D ≥ 2 := by nlinarith
  -- exp(B*f) = (4RD)^{2f}
  have hexpB : Real.exp (B * d.f) = (4 * R * D) ^ (2 * d.f) := by
    rw [show B * d.f = Real.log ((4 * R * D) ^ (2 * d.f)) from by
      rw [Real.log_pow]; push_cast; ring]
    exact Real.exp_log (by positivity)
  rw [hexpB]
  -- -------------------------
  -- Grid injection argument
  -- -------------------------
  -- Map each x ∈ X to a grid cell in (Fin (4*⌈RD⌉ + 1))^{2f}
  -- For each coordinate r, map x_r to (⌊2D * Re(x_r)⌉, ⌊2D * Im(x_r)⌉)
  -- All coordinates lie in [-R, R] so they land in a bounded grid
  -- The map is injective by the D^{-1}-separation
  -- -------------------------------------------------
  -- Use Set.ncard_le_of_injOn with injection into a Finset
  -- -------------------------------------------------
  -- The grid has at most (2*⌈2DR⌉ + 1)^{2f} cells, each with ≤ 1 element
  -- We bound by (4DR)^{2f} since 2*⌈2DR⌉ + 1 ≤ 4DR when 2DR ≥ 1
  -- For simplicity, we construct the Finset and injection
  -- Step 1: For x ∈ X, |Re(x r)| ≤ R and |Im(x r)| ≤ R (since |x r| ≤ supNorm x ≤ R)
  -- Step 2: 2D * Re(x r) ∈ [−2DR, 2DR], so the integer floor is in (-⌈2DR⌉, ..., ⌈2DR⌉)
  -- Step 3: This gives at most (2⌈2DR⌉ + 1)^{2f} cells
  -- We use a slightly different bound for cleanliness:
  -- Map x ↦ fun r => (Int.floor (2 * D * (x r).re), Int.floor (2 * D * (x r).im))
  -- Target Finset: Icc [−N, N]^{2f} where N = ⌈2DR⌉
  let N := Nat.ceil (2 * D * R)
  -- The total grid has (2N+1)^{2f} cells total; we bound by (4DR)^{2f}
  -- via (2N+1)^{2f} ≤ (4DR)^{2f} iff 2N+1 ≤ 4DR
  -- 2N+1 ≤ 2*(2DR) + 1 ≤ 2*(2DR) + 2*(2DR) = 4*(2DR)/... hmm
  -- Actually: 2N+1 ≤ 2*(2DR+1) ≤ 4DR*2 only if 1 ≤ 2DR
  -- We have 2DR ≥ 2*(1/2)*1 = 1 > 0, so N ≤ 2DR + 1 ≤ 2*2DR = 4DR iff 1 ≤ 2DR ✓
  -- So 2N+1 ≤ 2*(2DR)+1 ≤ ...
  -- Key: (2N+1) ≤ 4*D*R since 2N+1 ≤ 2*(2DR+1) = 4DR+2 ≤ 4*2DR = 8DR if DR ≥ 1... too loose
  -- Better bound: n ≤ (2N+1)^{2f} where 2N+1 ≤ 4DR (when 1 ≤ 2DR)
  -- Since 2DR ≥ 1 (R > 1/2, D ≥ 1): N ≤ 2DR, so 2N+1 ≤ 4DR+1 ≤ 4DR*(1+1/(4DR)) ≤ 4DR*2 but still larger
  --
  -- Alternative: avoid this subtlety by bounding n directly via X ⊆ supNormBall R
  -- and using the injection + explicit count
  --
  -- Cleanest: we show n ≤ (2N+1)^{2f} where (2N+1)^{2f} ≤ (4DR)^{2f}
  -- (2N+1) ≤ 4DR iff 1 ≤ 4DR - 2N = 4DR - 2⌈2DR⌉ ≥ 4DR - 2*(2DR+1) = -2 < 0. Not useful.
  --
  -- Use different bound: n ≤ (4DR)^{2f} directly from volume argument
  -- Injecting into integer grid of size (⌈4DR⌉)^{2f}:
  -- Map x ↦ fun r => (⌊(x r).re * 2D + 2DR⌋, ⌊(x r).im * 2D + 2DR⌋) ∈ (Fin (4DR+2))^{2f}
  -- This gives at most (⌈4DR⌉+1)^{2f} cells... still messy.
  --
  -- SIMPLEST APPROACH: use supNorm bound directly
  -- Since 2DR ≥ 1, N = ⌈2DR⌉ ≤ 2DR ≤ 2DR...
  -- Actually the cleanest is: show n ≤ (4*R*D)^{2f} via:
  -- 1. X is finite, so we can list elements x_1,...,x_n
  -- 2. For each pair x_i ≠ x_j: supNorm(x_i - x_j) ≥ D^{-1}
  -- 3. The open sup-balls B(x_i, D^{-1}/2) are disjoint and ⊆ supNorm ball (R + D^{-1}/2)
  -- 4. In ℝ^{2f}: vol(big ball) / vol(small ball) = ((R + D^{-1}/2) / (D^{-1}/2))^{2f} = (2RD+1)^{2f} ≤ (4RD)^{2f}
  --
  -- But we'd need MeasureTheory for step 3-4.
  -- Instead: pure grid (no measure theory):
  -- 5. Grid map ι: X → (Fin (4⌈RD⌉))^{2f} with ι(x) = (⌊2D*(x r).re + N⌋, ⌊2D*(x r).im + N⌋)_r
  -- 6. ι is injective
  -- 7. |Grid| ≤ (4⌈RD⌉)^{2f} ≤ (4RD + 4)^{2f} ≤ (8RD)^{2f}... still 8 not 4.
  --
  -- For exact bound 4RD: use VOLUME argument.
  -- The map x ↦ (x r - a r)_{r : Fin f} is the same as phi(β).
  -- We need to count β values.
  -- phi(β) lies in supNorm ball of radius 2R (since phi β = z - a, |z| ≤ R, but |a| could be anything).
  -- Actually |phi β r| = |z_r - a_r| ≤ |z_r| + |a_r| ≤ R + |a_r|... not bounded uniformly.
  --
  -- BUT: phi(β) - phi(β') = phi(β-β') has supNorm ≥ D^{-1} for β ≠ β'.
  -- And phi(β), phi(β') are both in the set {v | |a + v|_∞ ≤ R} = {v | |v_r + a_r| ≤ R ∀r}.
  -- The DIFFERENCES satisfy supNorm(phi(β-β')) ≤ supNorm(phi β) + supNorm(phi β') ≤ 2R (rough bound).
  -- But we need the cardinality bound on {phi β} ⊆ {v | supNorm(a + v) ≤ R}.
  -- The set {v | supNorm(a + v) ≤ R} = {v | |v_r + a_r| ≤ R ∀r} is a product of discs centered at -a_r.
  -- In ℝ^{2f} with sup-norm: this is a box of side 2R (in each real/imaginary direction).
  -- A D^{-1}-separated subset of this box has at most (2R / (D^{-1}/2))^{2f} = (4RD)^{2f} elements.
  -- This IS the packing argument but in a translated ball.
  -- For the grid approach: shift by a, then count.
  --
  -- We'll use: ncard X ≤ (4RD)^{2f} via integer grid injection.
  -- Grid cell size: D^{-1}/2 in each real/imaginary direction.
  -- For x ∈ X: |(x r).re + a r.re| ≤ R and |(x r).im + a r.im| ≤ R... no, |x r| ≤ R.
  -- Actually: supNorm x ≤ R means |x r| ≤ R, i.e., |(x r).re| ≤ R and |(x r).im| ≤ R.
  --
  -- Map x ↦ (⌊(x r).re * 2D⌋, ⌊(x r).im * 2D⌋)_{r : Fin f}
  -- Range: (⌊-2DR⌋, ..., ⌊2DR⌋)^{2f}. Number of grid cells: (2*⌊2DR⌋ + 1)^{2f}... messy.
  --
  -- CLEANEST APPROACH: Just do the bound via the Finset injection.
  -- The Finset is (Ico (⌊-2DR⌋) (⌈2DR⌉ + 1))^{2f} which has size (⌈2DR⌉ - ⌊-2DR⌋ + 1)^{2f} ≤ (⌈4DR⌉ + 1)^{2f}.
  -- And (⌈4DR⌉ + 1)^{2f} ≤ (4DR + 2)^{2f} ≤ (4DR)^{2f} * (1 + 1/(2DR))^{2f} ≤ (4DR)^{2f} * 2^{2f} when 2DR ≥ 1.
  -- This gives 8^{2f} * (DR)^{2f} but we need (4RD)^{2f}.
  --
  -- The bound (2RD+1)^{2f} ≤ (4RD)^{2f} IS correct when 2RD ≥ 1:
  -- 2RD + 1 ≤ 2*2RD = 4RD iff 1 ≤ 2RD. ✓
  -- But getting exactly (2RD+1)^{2f} from a grid argument needs careful setup.
  --
  -- I'll use a SLIGHTLY DIFFERENT injection that gives exactly (2RD+1)^{2f} ≤ (4RD)^{2f}:
  -- Map x ↦ (⌊x_r * 2D⌋, ⌊x_r.im * 2D⌋) ∈ (Fin (2*⌊2DR⌋+3))^{2f}
  -- Actually let me just bound ncard X ≤ (4*R*D)^{2f} using the injection.
  --
  -- =====================================================
  -- FINAL STRATEGY:
  -- Prove ncard X ≤ (2*R*D+1)^{2f}, then bound (2RD+1)^{2f} ≤ (4RD)^{2f}.
  -- =====================================================
  suffices h : (n : ℝ) ≤ (2 * R * D + 1) ^ (2 * d.f) by
    apply h.trans
    apply pow_le_pow_left₀ (by positivity)
    have h2RD1 : 2 * R * D ≥ 1 := by nlinarith
    linarith
  -- Prove n ≤ (2RD+1)^{2f} via the Haar-measure packing argument.
  -- Finitize X
  have hX_fin' : X.Finite := hX_fin
  let Xfin : Finset (Fin d.f → ℂ) := hX_fin'.toFinset
  have hXfin_coe : (Xfin : Set (Fin d.f → ℂ)) = X := hX_fin'.coe_toFinset
  have hXfin_card : Xfin.card = n := by
    rw [← Set.ncard_coe_finset, hXfin_coe]; rfl
  -- Elements of X are in the ball of radius R (in ‖·‖ = supNorm)
  have hXfin_ball : ∀ x ∈ Xfin, ‖x‖ ≤ R := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    rw [← supNorm_eq_norm]; exact hx.1
  -- Elements of X are D^{-1}-separated in ‖·‖
  have hD_pos : (0 : ℝ) < D := by rw [hD_def]; positivity
  have hDinv_pos : (0 : ℝ) < D⁻¹ := inv_pos.mpr hD_pos
  have hXfin_sep : ∀ x ∈ Xfin, ∀ y ∈ Xfin, x ≠ y → D⁻¹ ≤ ‖x - y‖ := by
    intro x hx y hy hne
    rw [Set.Finite.mem_toFinset] at hx hy
    rw [← supNorm_eq_norm]
    have hsep := cosetBall_separated d mld a R x y hx hy hne
    rwa [show (d.Q : ℝ) ^ (-(2:ℤ)) = D⁻¹ from by
      rw [hD_def]; rw [zpow_neg, zpow_ofNat]] at hsep
  -- Apply packing bound with δ = D^{-1}
  have hpack : (Xfin.card : ℝ) ≤ (2 * R / D⁻¹ + 1) ^ (2 * d.f) :=
    packing_bound_fin d.f Xfin R D⁻¹ hDinv_pos (by linarith) hXfin_ball hXfin_sep
  -- Simplify: 2R / D⁻¹ + 1 = 2RD + 1
  have hsimp : (2 * R / D⁻¹ + 1) = 2 * R * D + 1 := by
    field_simp
  rw [hXfin_card, hsimp] at hpack
  exact_mod_cast hpack

end UnitDistance
