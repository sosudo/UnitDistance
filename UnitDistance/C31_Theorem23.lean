import Mathlib
import UnitDistance.C01_UnitDistanceFunctions
import UnitDistance.C02_AdmissibleDatum
import UnitDistance.C21_NormOneSetU
import UnitDistance.C28_Lemma24
import UnitDistance.C29_Lemma25
import UnitDistance.C210_Lemma26

set_option linter.style.longLine false

namespace UnitDistance

open Real NumberField Filter Topology

/-- Helper: unitDistancePairs P ≤ P.card^2 (from the definition) -/
private lemma unitDistancePairs_le_sq (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    (unitDistancePairs P : ℝ) ≤ (P.card : ℝ) ^ 2 := by
  have : unitDistancePairs P ≤ P.card ^ 2 := by
    unfold unitDistancePairs
    calc ((P ×ˢ P).filter _).card / 2
        ≤ (P ×ˢ P).card / 2 := Nat.div_le_div_right (Finset.card_filter_le _ _)
      _ ≤ (P ×ˢ P).card := Nat.div_le_self _ _
      _ = P.card * P.card := Finset.card_product _ _
      _ = P.card ^ 2 := by ring
  exact_mod_cast this

/-- Helper: maxUnitDistancePairs n ≥ unitDistancePairs P when P.card = n -/
private lemma maxUDP_ge (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    (unitDistancePairs P : ℝ) ≤ (maxUnitDistancePairs P.card : ℝ) := by
  suffices h : unitDistancePairs P ≤ maxUnitDistancePairs P.card by exact_mod_cast h
  unfold maxUnitDistancePairs
  apply le_csSup
  · refine ⟨P.card ^ 2, fun k ⟨Q, hQ_card, hQ_udp⟩ => ?_⟩
    rw [← hQ_udp]
    have := unitDistancePairs_le_sq Q
    have hQsq : unitDistancePairs Q ≤ Q.card ^ 2 := by exact_mod_cast this
    calc unitDistancePairs Q ≤ Q.card ^ 2 := hQsq
      _ = P.card ^ 2 := by rw [hQ_card]
  · exact ⟨P, rfl, rfl⟩

/-- Helper: NeZero from positivity -/
private lemma data_f_pos (d : AdmissibleDatum) : 0 < d.f := by
  unfold AdmissibleDatum.f
  letI := d.fieldL; letI := d.numberFieldL
  exact Module.finrank_pos (R := ℚ) (M := d.L)

/-- Helper: construct MinkowskiLatticeData using a fixed ring hom -/
private noncomputable def mkMinkowskiLatticeData (d : AdmissibleDatum) [NeZero d.f]
    (U : Finset d.K)
    (hU_norm : letI := d.fieldK; letI := d.charZeroK; letI := d.numberFieldK;
      ∀ u ∈ U, ∀ φ : d.K →+* ℂ, ‖φ u‖ = 1)
    (hU_integral : letI := d.fieldK; letI := d.charZeroK; letI := d.numberFieldK;
      ∀ u ∈ U, IsIntegral ℤ ((d.Q : d.K) ^ 2 * u)) :
    MinkowskiLatticeData d := by
  letI := d.fieldK; letI := d.charZeroK; letI := d.numberFieldK
  haveI : Nonempty (d.K →+* ℂ) := inferInstance
  exact {
    phi := fun k _ => Classical.arbitrary (d.K →+* ℂ) k
    U := U
    U_norm_one := fun u hu _ => hU_norm u hu (Classical.arbitrary _)
    U_integral := hU_integral
    phi_coord_injective := by
      intro r k₁ k₂ h
      -- h : Classical.arbitrary (d.K →+* ℂ) k₁ = Classical.arbitrary (d.K →+* ℂ) k₂
      exact RingHom.injective (Classical.arbitrary (d.K →+* ℂ)) h
  }

/-- Theorem 2.3: Given a sequence of admissible data with fixed primes q₁,...,qₜ,
    degrees f_j → ∞, and class number bound h(K_j) ≤ H^{f_j} with γ = t·log2 - logH > 0,
    there exists δ > 0 and infinitely many n with ν(n) ≥ n^{1+δ}. -/
theorem theorem23_admissibleToNu
    (t : ℕ) (ht : 1 ≤ t)
    (H : ℝ) (hH : H > 0)
    (γ : ℝ) (hγ : γ = t * Real.log 2 - Real.log H) (hγpos : γ > 0)
    (data : ℕ → AdmissibleDatum)
    (hdata_t : ∀ j, (data j).t = t)
    (hdata_primes : ∀ j (i : Fin t),
        (data j).primes (i.cast (hdata_t j).symm) = (data 0).primes (i.cast (hdata_t 0).symm))
    (hdata_fGrowing : ∀ M : ℕ, ∃ j, M ≤ (data j).f)
    (hdata_classNum : ∀ j,
      letI := (data j).fieldK
      letI := (data j).numberFieldK
      (Fintype.card (ClassGroup (𝓞 (data j).K)) : ℝ) ≤ H ^ (data j).f) :
    ∃ δ : ℝ, δ > 0 ∧
      ∃ nseq : ℕ → ℕ,
        (∀ j, nseq j < nseq (j+1)) ∧
        (∀ j, (maxUnitDistancePairs (nseq j) : ℝ) ≥ (nseq j : ℝ) ^ (1 + δ)) := by
  -- =====================================================================
  -- Step 1: Extract R with log(ρ_R) > -γ/2
  -- =====================================================================
  obtain ⟨R, hR_pos, hR_good⟩ :
      ∃ R : ℝ, R > 1 / 2 ∧ Real.log (discOverlapRatio R) > -(γ / 2) := by
    have hlog_tend : Tendsto (fun R => Real.log (discOverlapRatio R)) atTop (nhds 0) := by
      have h : Tendsto (fun R => Real.log (discOverlapRatio R)) atTop (nhds (Real.log 1)) :=
        (Real.continuousAt_log (by norm_num)).tendsto.comp discOverlapRatio_tendsto_one
      rwa [Real.log_one] at h
    have hε : (0 : ℝ) < γ / 2 := by linarith
    have hev : ∀ᶠ R in atTop, Real.log (discOverlapRatio R) > -(γ / 2) := by
      have h0 : (fun R : ℝ => Real.log (discOverlapRatio R)) ⁻¹' {x | x > -(γ/2)} ∈ atTop :=
        hlog_tend (isOpen_Ioi.mem_nhds (by simp; linarith))
      exact h0
    exact ((eventually_gt_atTop (1/2 : ℝ)).and hev).exists.imp fun R ⟨h1, h2⟩ => ⟨h1, h2⟩
  -- =====================================================================
  -- Step 2: Fixed constants B and D
  -- =====================================================================
  have hQ_fixed : ∀ j, (data j).Q = (data 0).Q := by
    intro j; unfold AdmissibleDatum.Q
    have s1 : ∏ i : Fin (data j).t, (data j).primes i =
        ∏ i : Fin t, (data j).primes (i.cast (hdata_t j).symm) :=
      Fintype.prod_equiv (Fin.castOrderIso (hdata_t j)).toEquiv _ _ (fun i => by simp)
    have s2 : ∏ i : Fin (data 0).t, (data 0).primes i =
        ∏ i : Fin t, (data 0).primes (i.cast (hdata_t 0).symm) :=
      Fintype.prod_equiv (Fin.castOrderIso (hdata_t 0)).toEquiv _ _ (fun i => by simp)
    rw [s1, s2]; congr 1; funext i; exact hdata_primes j i
  let D : ℝ := ((data 0).Q : ℝ) ^ 2
  let B : ℝ := 2 * Real.log (4 * R * D)
  have hQ0_ge1 : (data 0).Q ≥ 1 :=
    Finset.one_le_prod' (fun i _ => (data 0).primePrime i |>.one_le)
  have hD_ge1 : D ≥ 1 := by
    show ((data 0).Q : ℝ)^2 ≥ 1
    have : (1 : ℝ) ≤ ((data 0).Q : ℝ) := by exact_mod_cast hQ0_ge1
    nlinarith [sq_nonneg ((data 0).Q : ℝ)]
  have hB_pos : B > 0 := by
    show 2 * Real.log (4 * R * ((data 0).Q : ℝ)^2) > 0
    apply mul_pos (by norm_num); apply Real.log_pos; nlinarith
  have hδ_pos : γ / (4 * B) > 0 := by positivity
  refine ⟨γ / (4 * B), hδ_pos, ?_⟩
  -- =====================================================================
  -- Step 3: Per-j structures
  -- =====================================================================
  have hf_pos : ∀ j, 0 < (data j).f := fun j => data_f_pos (data j)
  have hNeZero : ∀ j, NeZero (data j).f := fun j => ⟨Nat.pos_iff_ne_zero.mp (hf_pos j)⟩
  have hγ_j : ∀ j, γ = (data j).t * Real.log 2 - Real.log H := fun j => by rw [hγ, hdata_t]
  -- For each j, get U_j from normOneSetU
  have hU_exists : ∀ j, ∃ (U : Finset (data j).K),
      (letI := (data j).fieldK; letI := (data j).charZeroK; letI := (data j).numberFieldK;
       ∀ u ∈ U, ∀ φ : (data j).K →+* ℂ, ‖φ u‖ = 1) ∧
      ((U.card : ℝ) ≥ Real.exp (γ * (data j).f)) ∧
      (letI := (data j).fieldK; letI := (data j).charZeroK; letI := (data j).numberFieldK;
       ∀ u ∈ U, IsIntegral ℤ (((data j).Q : (data j).K) ^ 2 * u)) := by
    intro j
    letI := (data j).fieldK; letI := (data j).charZeroK; letI := (data j).numberFieldK
    letI := (data j).cmFieldK; letI := (data j).algebraLK
    letI := (data j).fieldL; letI := (data j).numberFieldL
    obtain ⟨U, -, hU_norm, hU_size, hU_int⟩ := normOneSetU_exists (data j) H hH (hdata_classNum j)
    have hU_size' : (U.card : ℝ) ≥ Real.exp (γ * (data j).f) :=
      calc (U.card : ℝ) ≥ Real.exp (((data j).t * Real.log 2 - Real.log H) * (data j).f) := hU_size
        _ = Real.exp (γ * (data j).f) := by congr 1; rw [← hγ_j j]
    exact ⟨U, hU_norm, hU_size', hU_int⟩
  -- =====================================================================
  -- Step 4: For each j, construct Pfin_j via lemmas 24, 25, 26
  -- =====================================================================
  have hPfin_exists : ∀ j, ∃ (Pfin : Finset (EuclideanSpace ℝ (Fin 2))),
      (Pfin.card : ℝ) ≥ 1 ∧
      (Pfin.card : ℝ) ≤ Real.exp (B * (data j).f) ∧
      (unitDistancePairs Pfin : ℝ) ≥ (1/2) * Real.exp (γ * (data j).f / 2) * Pfin.card := by
    intro j
    haveI hNZ := hNeZero j
    obtain ⟨U_j, hU_norm, hU_size, hU_int⟩ := hU_exists j
    letI := (data j).fieldK; letI := (data j).charZeroK; letI := (data j).numberFieldK
    let mld := mkMinkowskiLatticeData (data j) U_j hU_norm hU_int
    obtain ⟨a_j, ha_nonempty, ha_good⟩ := lemma24_cosetAveraging
      (data j) H hH γ (hγ_j j) hγpos mld hU_size R hR_pos hR_good
    obtain ⟨hinj, Pfin_j, hPcard, hν_bound⟩ :=
      lemma25_injectivity_nuBound (data j) mld H γ R hH hγpos hR_pos a_j ha_nonempty ha_good
    -- The projection π₁ used in lemma25
    let π₁ : (Fin (data j).f → ℂ) → ℂ :=
      fun z => z ⟨0, Nat.pos_of_ne_zero (NeZero.ne (data j).f)⟩
    let X := cosetBallIntersection (data j) mld a_j R
    -- hPcard: (Pfin_j.card : ℝ) = Set.ncard (π₁ '' X)
    -- hinj: Set.InjOn π₁ X
    -- Pfin_j.card = cosetCount via injectivity
    have hPcard_eq : Pfin_j.card = cosetCount (data j) mld a_j R := by
      have h1 : Set.ncard (π₁ '' X) = Set.ncard X := hinj.ncard_image
      have h2 : (Pfin_j.card : ℝ) = (Set.ncard X : ℝ) := hPcard.trans (by exact_mod_cast h1)
      exact_mod_cast h2
    -- cosetCount ≥ 1 from ha_nonempty
    have hN_ge1 : (Pfin_j.card : ℝ) ≥ 1 := by
      rw [show (Pfin_j.card : ℝ) = (cosetCount (data j) mld a_j R : ℝ) by
          exact_mod_cast hPcard_eq]
      have hN_nat : cosetCount (data j) mld a_j R ≥ 1 :=
        Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (by exact_mod_cast ha_nonempty))
      exact_mod_cast hN_nat
    -- packing bound
    have hB_eq_j : 2 * Real.log (4 * R * ((data j).Q : ℝ) ^ 2) = B := by
      show 2 * Real.log (4 * R * ((data j).Q : ℝ)^2) = 2 * Real.log (4 * R * ((data 0).Q : ℝ)^2)
      have : (data j).Q = (data 0).Q := hQ_fixed j
      simp only [this]
    have hpack : (Pfin_j.card : ℝ) ≤ Real.exp (B * (data j).f) := by
      rw [show (Pfin_j.card : ℝ) = (cosetCount (data j) mld a_j R : ℝ) by
          exact_mod_cast hPcard_eq]
      calc (cosetCount (data j) mld a_j R : ℝ)
          ≤ Real.exp (2 * Real.log (4 * R * ((data j).Q : ℝ) ^ 2) * (data j).f) :=
            lemma26_packingBound (data j) mld γ R hR_pos hγpos a_j ha_nonempty ha_good
        _ = Real.exp (B * (data j).f) := by rw [hB_eq_j]
    -- nu bound
    have hν : (unitDistancePairs Pfin_j : ℝ) ≥
        (1/2) * Real.exp (γ * (data j).f / 2) * Pfin_j.card := by
      -- hν_bound: ≥ (1/2) * exp * ncard (π₁ '' X)
      -- hinj.ncard_image: ncard (π₁ '' X) = ncard X = cosetCount = Pfin_j.card
      have hXeq : Set.ncard X = Set.ncard (π₁ '' X) := hinj.ncard_image.symm
      have hcardX : (Set.ncard X : ℝ) = Pfin_j.card := by
        exact_mod_cast hPcard_eq.symm
      calc (unitDistancePairs Pfin_j : ℝ)
          ≥ (1/2) * Real.exp (γ * (data j).f / 2) * Set.ncard (π₁ '' X) := hν_bound
        _ = (1/2) * Real.exp (γ * (data j).f / 2) * Set.ncard X := by rw [hinj.ncard_image]
        _ = (1/2) * Real.exp (γ * (data j).f / 2) * Pfin_j.card := by rw [hcardX]
    exact ⟨Pfin_j, hN_ge1, hpack, hν⟩
  -- =====================================================================
  -- Step 5: Show infinitely many good n (n with maxUDP n ≥ n^{1+δ})
  -- =====================================================================
  have hgood_large : ∀ M : ℕ, ∃ n : ℕ, n > M ∧
      (maxUnitDistancePairs n : ℝ) ≥ (n : ℝ) ^ (1 + γ / (4 * B)) := by
    intro M
    let F₀ := Nat.ceil (4 * Real.log 2 / γ) + 1
    let F₁ := Nat.ceil (2 * Real.log (2 * M + 2) / γ) + 1
    let F := max F₀ F₁
    obtain ⟨j, hj_fF⟩ := hdata_fGrowing F
    obtain ⟨Pfin_j, hn_ge1, hn_le, hν⟩ := hPfin_exists j
    set n_j := Pfin_j.card with hn_j_def
    -- Establish ν ≤ n_j²
    have hν_le_sq := unitDistancePairs_le_sq Pfin_j
    -- n_j ≥ 1/2 * exp(γ * f_j / 2)
    have hn_large_exp : (n_j : ℝ) ≥ 1/2 * Real.exp (γ * (data j).f / 2) := by
      have hn_pos : (n_j : ℝ) > 0 := by linarith
      nlinarith [sq_nonneg (n_j : ℝ), Real.exp_pos (γ * ↑(data j).f / 2)]
    -- f_j ≥ F₁
    have hfj_ge_F1 : (data j).f ≥ F₁ := le_trans (le_max_right F₀ F₁) hj_fF
    have hF1_bound : (F₁ : ℝ) ≥ 2 * Real.log (2 * M + 2) / γ := by
      simp only [F₁]; push_cast; linarith [Nat.le_ceil (2 * Real.log (2 * M + 2) / γ)]
    have hexp_M : Real.exp (γ * (data j).f / 2) ≥ 2 * M + 2 := by
      rw [ge_iff_le, ← Real.log_le_iff_le_exp (by positivity)]
      calc Real.log (2 * ↑M + 2) = γ * (2 * Real.log (2 * ↑M + 2) / γ) / 2 := by field_simp
        _ ≤ γ * F₁ / 2 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            exact mul_le_mul_of_nonneg_left hF1_bound (le_of_lt hγpos)
        _ ≤ γ * (data j).f / 2 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hfj_ge_F1) (le_of_lt hγpos)
    have hn_gt_M : n_j > M := by
      have : (n_j : ℝ) ≥ M + 1 := by
        have step1 : (1 : ℝ)/2 * Real.exp (γ * ↑(data j).f / 2) ≥ (1 : ℝ)/2 * (2 * ↑M + 2) :=
          mul_le_mul_of_nonneg_left hexp_M (by norm_num)
        have step2 : (1 : ℝ)/2 * (2 * ↑M + 2) = ↑M + 1 := by ring
        linarith
      exact_mod_cast this
    -- n_j^δ ≤ exp(γ * f_j / 4)
    have hn_pos : (0 : ℝ) < n_j := by linarith
    have hn_rpow_le : (n_j : ℝ) ^ (γ / (4 * B)) ≤ Real.exp (γ * (data j).f / 4) := by
      calc (n_j : ℝ) ^ (γ / (4 * B))
          ≤ Real.exp (B * (data j).f) ^ (γ / (4 * B)) :=
            Real.rpow_le_rpow (by positivity) hn_le (by positivity)
        _ = Real.exp (γ * (data j).f / 4) := by
            rw [← Real.exp_mul]; congr 1; field_simp
    -- f_j ≥ F₀, so exp(γ * f_j / 4) ≥ 2
    have hfj_ge_F0 : (data j).f ≥ F₀ := le_trans (le_max_left F₀ F₁) hj_fF
    have hF0_bound : (F₀ : ℝ) ≥ 4 * Real.log 2 / γ := by
      simp only [F₀]; push_cast; linarith [Nat.le_ceil (4 * Real.log 2 / γ)]
    have hexp4_ge2 : Real.exp (γ * (data j).f / 4) ≥ 2 := by
      rw [ge_iff_le, ← Real.log_le_iff_le_exp (by norm_num)]
      calc Real.log 2 = γ * (4 * Real.log 2 / γ) / 4 := by field_simp
        _ ≤ γ * F₀ / 4 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            exact mul_le_mul_of_nonneg_left hF0_bound (le_of_lt hγpos)
        _ ≤ γ * (data j).f / 4 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hfj_ge_F0) (le_of_lt hγpos)
    -- (1/2) * exp(γ * f_j / 2) ≥ exp(γ * f_j / 4)
    have hbound : (1/2) * Real.exp (γ * (data j).f / 2) ≥ Real.exp (γ * (data j).f / 4) := by
      have heq : Real.exp (γ * (data j).f / 2) =
          Real.exp (γ * (data j).f / 4) * Real.exp (γ * (data j).f / 4) := by
        rw [← Real.exp_add]; congr 1; ring
      nlinarith [Real.exp_pos (γ * (data j).f / 4)]
    -- ν_j ≥ n_j^{1+δ}
    have hν_ge_pow : (unitDistancePairs Pfin_j : ℝ) ≥ (n_j : ℝ) ^ (1 + γ / (4 * B)) := by
      rw [Real.rpow_add (by positivity), Real.rpow_one]
      -- goal: ↑(unitDistancePairs Pfin_j) ≥ ↑n_j * ↑n_j ^ (γ / (4 * B))
      have hmul_comm : (n_j : ℝ) * (n_j : ℝ) ^ (γ / (4 * B)) = (n_j : ℝ) ^ (γ / (4 * B)) * n_j := by ring
      rw [hmul_comm]
      calc (n_j : ℝ) ^ (γ / (4 * B)) * n_j
          ≤ Real.exp (γ * (data j).f / 4) * n_j :=
            mul_le_mul_of_nonneg_right hn_rpow_le (by positivity)
        _ ≤ (1/2) * Real.exp (γ * (data j).f / 2) * n_j :=
            mul_le_mul_of_nonneg_right hbound (by positivity)
        _ ≤ (unitDistancePairs Pfin_j : ℝ) := hν
    -- maxUDP ≥ ν_j ≥ n_j^{1+δ}
    have hmax_ge : (maxUnitDistancePairs n_j : ℝ) ≥ unitDistancePairs Pfin_j :=
      maxUDP_ge Pfin_j
    exact ⟨n_j, hn_gt_M, le_trans hν_ge_pow hmax_ge⟩
  -- =====================================================================
  -- Step 6: Extract strictly increasing nseq
  -- =====================================================================
  -- G := {n | maxUDP n ≥ n^{1+δ}} is infinite (from hgood_large)
  -- Extract nseq by Classical.choose recursion
  let next : ℕ → ℕ := fun M => Classical.choose (hgood_large M)
  have hnext_gt : ∀ M, next M > M := fun M => (Classical.choose_spec (hgood_large M)).1
  have hnext_good : ∀ M, (maxUnitDistancePairs (next M) : ℝ) ≥ (next M : ℝ) ^ (1 + γ / (4 * B)) := by
    intro M; exact (Classical.choose_spec (hgood_large M)).2
  let nseq : ℕ → ℕ := fun k => Nat.rec (next 0) (fun _ nk => next nk) k
  refine ⟨nseq, ?_, ?_⟩
  · -- Strictly increasing
    intro k
    exact hnext_gt (nseq k)
  · -- ν bound
    intro k
    induction k with
    | zero => exact hnext_good 0
    | succ k' _ => exact hnext_good (nseq k')

end UnitDistance
