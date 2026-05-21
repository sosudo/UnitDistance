import Mathlib
import UnitDistance.C01_UnitDistanceFunctions
import UnitDistance.C02_AdmissibleDatum
import UnitDistance.C06_CMFields
import UnitDistance.C20_MinkowskiLattice
import UnitDistance.C28_Lemma24

set_option linter.style.longLine false

namespace UnitDistance

open Real Complex

/-- Injectivity of first-coordinate projection on cosetBallIntersection. -/
private theorem pi1_injOn_cosetBall (d : AdmissibleDatum) [NeZero d.f]
    (mld : MinkowskiLatticeData d) (a : Fin d.f → ℂ) (R : ℝ) :
    letI := d.fieldK; letI := d.charZeroK; letI := d.numberFieldK
    Set.InjOn (fun z : Fin d.f → ℂ => z ⟨0, Nat.pos_of_ne_zero (NeZero.ne d.f)⟩)
              (cosetBallIntersection d mld a R) := by
  letI hfK := d.fieldK; letI hcK := d.charZeroK; letI hnK := d.numberFieldK
  intro x hx x' hx' heq
  obtain ⟨v, hv_mem, rfl⟩ := hx.2
  obtain ⟨v', hv'_mem, rfl⟩ := hx'.2
  simp only [minkowskiLattice, Set.mem_range] at hv_mem hv'_mem
  obtain ⟨⟨β, hβ_int⟩, rfl⟩ := hv_mem
  obtain ⟨⟨β', hβ'_int⟩, rfl⟩ := hv'_mem
  simp only [Pi.add_apply] at heq
  have hphi0 : mld.phi β ⟨0, Nat.pos_of_ne_zero (NeZero.ne d.f)⟩ =
               mld.phi β' ⟨0, Nat.pos_of_ne_zero (NeZero.ne d.f)⟩ :=
    add_left_cancel heq
  have hβeq : β = β' := mld.phi_coord_injective _ hphi0
  have hphi_eq : mld.phi (⟨β, hβ_int⟩ : {x : d.K // IsIntegral ℤ ((d.Q : d.K)^2 * x)}).val =
                 mld.phi (⟨β', hβ'_int⟩ : {x : d.K // IsIntegral ℤ ((d.Q : d.K)^2 * x)}).val :=
    congrArg mld.phi hβeq
  rw [hphi_eq]

/-- Lemma 2.5 (Injectivity and ν-bound). -/
theorem lemma25_injectivity_nuBound
    (d : AdmissibleDatum) [NeZero d.f]
    (mld : MinkowskiLatticeData d)
    (H γ R : ℝ) (hH : H > 0) (hγpos : γ > 0) (hR : R > 1 / 2)
    (a : Fin d.f → ℂ)
    (hcoset_nonempty : (cosetCount d mld a R : ℝ) > 0)
    (hcoset_good : (unitPairCount d mld a R : ℝ) ≥
                    Real.exp (γ * d.f / 2) * cosetCount d mld a R) :
    let X := cosetBallIntersection d mld a R
    let π₁ : (Fin d.f → ℂ) → ℂ := fun z => z ⟨0, Nat.pos_of_ne_zero (NeZero.ne d.f)⟩
    let P := π₁ '' X
    Set.InjOn π₁ X ∧
    ∃ Pfin : Finset (EuclideanSpace ℝ (Fin 2)),
      (Pfin.card : ℝ) = Set.ncard P ∧
      (unitDistancePairs Pfin : ℝ) ≥
        (1 / 2) * Real.exp (γ * d.f / 2) * Set.ncard P := by
  letI hfK := d.fieldK; letI hcK := d.charZeroK; letI hnK := d.numberFieldK
  let f0 : 0 < d.f := Nat.pos_of_ne_zero (NeZero.ne d.f)
  let X := cosetBallIntersection d mld a R
  let π₁ : (Fin d.f → ℂ) → ℂ := fun z => z ⟨0, f0⟩
  -- (a) Injectivity of π₁ on X
  have hinj : Set.InjOn π₁ X := pi1_injOn_cosetBall d mld a R
  -- Finiteness
  have hcoset_pos : 0 < cosetCount d mld a R := by exact_mod_cast hcoset_nonempty
  have hX_fin : X.Finite := Set.finite_of_ncard_pos hcoset_pos
  have hP_fin : (π₁ '' X).Finite := hX_fin.image π₁
  -- ncard P = ncard X = cosetCount
  have hPcard_eq : Set.ncard (π₁ '' X) = Set.ncard X := hinj.ncard_image
  -- Isometry ℂ ≃ₗᵢ EuclideanSpace ℝ (Fin 2)
  let cTE : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)
  -- Construct Pfin
  let Pc : Finset ℂ := hP_fin.toFinset
  have hPc_coe : (Pc : Set ℂ) = π₁ '' X := hP_fin.coe_toFinset
  let Pfin : Finset (EuclideanSpace ℝ (Fin 2)) := Pc.image cTE
  -- Pfin.card = ncard P
  have hPfin_card : (Pfin.card : ℝ) = Set.ncard (π₁ '' X) := by
    have hcard : Pfin.card = Pc.card := Finset.card_image_of_injective Pc cTE.injective
    rw [hcard, ← Set.ncard_coe_finset Pc, hPc_coe]
  -- cosetCount = ncard P as reals
  have hcoset_eq : (cosetCount d mld a R : ℝ) = (Set.ncard (π₁ '' X) : ℝ) := by
    simp only [cosetCount]; exact_mod_cast hPcard_eq.symm
  -- Define filter F
  let F := (Pfin ×ˢ Pfin).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1)
  -- 2 ∣ F.card via swap involution
  have hF_even : 2 ∣ F.card := by
    -- sum_involution: ∑ p ∈ F, 1 = 0 in ZMod 2
    have hsum : ∑ _p ∈ F, (1 : ZMod 2) = 0 :=
      Finset.sum_involution (fun p _ => Prod.swap p)
        (fun _ _ => by decide)
        (fun p hp hne => by
          simp only [F, Finset.mem_filter, Finset.mem_product] at hp
          intro heq_swap
          have hswap : Prod.swap p = p := heq_swap
          have := congr_arg Prod.fst hswap
          simp [Prod.swap] at this
          exact hp.2.1 this.symm)
        (fun p hp => by
          simp only [F, Finset.mem_filter, Finset.mem_product] at hp ⊢
          simp only [Prod.swap]
          refine ⟨⟨hp.1.2, hp.1.1⟩, ?_, ?_⟩
          · exact fun h => hp.2.1 h.symm
          · rw [dist_comm]; exact hp.2.2)
        (fun p _ => Prod.swap_swap p)
    -- Deduce 2 | F.card
    have : (F.card : ZMod 2) = 0 := by
      have : ∑ _p ∈ F, (1 : ZMod 2) = F.card • (1 : ZMod 2) := Finset.sum_const _
      rw [this] at hsum
      simpa using hsum
    exact (ZMod.natCast_eq_zero_iff F.card 2).mp this
  -- F.card = 2 * unitDistancePairs Pfin
  have hF_eq : F.card = 2 * unitDistancePairs Pfin := by
    have hud : unitDistancePairs Pfin = F.card / 2 := rfl
    obtain ⟨k, hk⟩ := hF_even
    omega
  -- Injection: F.card ≥ unitPairCount (in ℕ)
  have hF_ge_unitPair : F.card ≥ unitPairCount d mld a R := by
    -- The unitPairCount set
    let S := {p : (Fin d.f → ℂ) × (Fin d.f → ℂ) |
                p.1 ∈ X ∧ p.2 ∈ X ∧ p.2 - p.1 ∈ imageU d mld}
    have hS_fin : S.Finite := (hX_fin.prod hX_fin).subset (fun p hp => ⟨hp.1, hp.2.1⟩)
    -- ncard S = unitPairCount
    have hS_ncard : Set.ncard S = unitPairCount d mld a R := by
      have : S = {p : (Fin d.f → ℂ) × (Fin d.f → ℂ) |
                    p.1 ∈ cosetBallIntersection d mld a R ∧
                    p.2 ∈ cosetBallIntersection d mld a R ∧
                    p.2 - p.1 ∈ imageU d mld} := rfl
      simp [unitPairCount, ← this]
    -- injection map
    let φ : (Fin d.f → ℂ) × (Fin d.f → ℂ) → EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) :=
      fun p => (cTE (π₁ p.1), cTE (π₁ p.2))
    -- Membership in Pc helper
    have hPc_mem : ∀ z ∈ π₁ '' X, cTE z ∈ Pfin := by
      intro z hz
      apply Finset.mem_image.mpr
      exact ⟨z, Finset.mem_coe.mp (hPc_coe ▸ hz), rfl⟩
    -- φ maps S into F
    have hφ_maps : ∀ p ∈ hS_fin.toFinset, φ p ∈ F := by
      intro p hp
      rw [Set.Finite.mem_toFinset] at hp
      simp only [F, Finset.mem_filter, Finset.mem_product, φ]
      obtain ⟨hp1, hp2, hu⟩ := hp
      have hpfin1 : cTE (π₁ p.1) ∈ Pfin := hPc_mem _ (Set.mem_image_of_mem π₁ hp1)
      have hpfin2 : cTE (π₁ p.2) ∈ Pfin := hPc_mem _ (Set.mem_image_of_mem π₁ hp2)
      obtain ⟨u, hu_mem, hu_eq⟩ := hu
      have hphi0 : π₁ p.2 - π₁ p.1 = mld.phi u ⟨0, f0⟩ := by
        have := (congr_fun hu_eq ⟨0, f0⟩).symm
        simp only [Pi.sub_apply] at this
        exact this
      have hnorm1 : ‖mld.phi u ⟨0, f0⟩‖ = 1 := mld.U_norm_one u hu_mem ⟨0, f0⟩
      have hdist1 : dist (cTE (π₁ p.1)) (cTE (π₁ p.2)) = 1 := by
        rw [cTE.isometry.dist_eq, dist_eq_norm, norm_sub_rev, hphi0, hnorm1]
      refine ⟨⟨hpfin1, hpfin2⟩, ?_, hdist1⟩
      intro heq
      rw [heq, dist_self] at hdist1
      norm_num at hdist1
    -- φ is injective on S
    have hφ_inj : Set.InjOn φ hS_fin.toFinset := by
      intro p hp q hq heq
      rw [hS_fin.coe_toFinset] at hp hq
      simp only [φ, Prod.mk.injEq] at heq
      exact Prod.ext (hinj hp.1 hq.1 (cTE.injective heq.1))
                     (hinj hp.2.1 hq.2.1 (cTE.injective heq.2))
    -- card inequality
    have hcard_le : hS_fin.toFinset.card ≤ F.card :=
      Finset.card_le_card_of_injOn φ hφ_maps hφ_inj
    have hS_card : hS_fin.toFinset.card = unitPairCount d mld a R := by
      rw [← hS_ncard, Set.ncard_eq_toFinset_card S hS_fin]
    omega
  -- F.card ≥ exp * N in ℝ
  have hF_ge_exp : (F.card : ℝ) ≥ Real.exp (γ * d.f / 2) * Set.ncard (π₁ '' X) := by
    calc (F.card : ℝ) ≥ unitPairCount d mld a R := by exact_mod_cast hF_ge_unitPair
      _ ≥ Real.exp (γ * d.f / 2) * cosetCount d mld a R := hcoset_good
      _ = Real.exp (γ * d.f / 2) * Set.ncard (π₁ '' X) := by rw [hcoset_eq]
  -- Conclude
  refine ⟨hinj, Pfin, hPfin_card, ?_⟩
  have htwice : (2 * unitDistancePairs Pfin : ℝ) ≥ Real.exp (γ * d.f / 2) * Set.ncard (π₁ '' X) := by
    have hcast : (F.card : ℝ) = 2 * unitDistancePairs Pfin := by exact_mod_cast hF_eq
    linarith
  linarith

end UnitDistance
