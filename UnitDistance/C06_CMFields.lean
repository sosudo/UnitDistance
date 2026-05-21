import Mathlib
import UnitDistance.C03_BasicFieldConventions

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UnitDistance.NumberTheory

open NumberField ComplexEmbedding InfinitePlace
open scoped ComplexConjugate

/-!
# CM Fields

A CM field is a totally imaginary quadratic extension K/K⁺ of a totally real field K⁺.
In this paper, K = L(i) where L is totally real, and complex conjugation c acts by
c(a + bi) = a - bi.

The key properties formalized here:
- The complex conjugation automorphism c : K ≃ₐ[K⁺] K
- For u ∈ K×: u · c(u) = 1 iff ‖σ(u)‖ = 1 for all complex embeddings σ
- N_{K/L}(u) = u · c(u) for K = L(i)
-/

variable (K : Type*) [Field K] [NumberField K] [CharZero K]
  [Algebra.IsIntegral ℚ K] [IsCMField K]

local notation3 "K⁺" => maximalRealSubfield K

/-- The complex conjugation automorphism of a CM field K over its maximal real subfield K⁺.
    This is the unique nontrivial element of Gal(K/K⁺). -/
noncomputable def cmComplexConj : K ≃ₐ[K⁺] K :=
  IsCMField.complexConj K

/-- The complex conjugation is nontrivial. -/
theorem cmComplexConj_ne_one : cmComplexConj K ≠ (1 : K ≃ₐ[K⁺] K) :=
  IsCMField.complexConj_ne_one K

/-- The complex conjugation is an involution: c(c(u)) = u. -/
theorem cmComplexConj_involutive (u : K) :
    cmComplexConj K (cmComplexConj K u) = u :=
  IsCMField.complexConj_apply_apply K u

/-- For a complex embedding φ : K → ℂ, φ(c(u)) = conj(φ(u)).
    This encodes the defining property of complex conjugation. -/
theorem cmComplexConj_embedding (φ : K →+* ℂ) (u : K) :
    φ (cmComplexConj K u) = conj (φ u) := by
  simp only [cmComplexConj, IsCMField.complexEmbedding_complexConj K φ u, starRingEnd_apply]

/-- For u in K, the complex conjugation preserves the norm at every infinite place. -/
theorem cmComplexConj_infinitePlace (w : InfinitePlace K) (u : K) :
    w (cmComplexConj K u) = w u :=
  IsCMField.infinitePlace_complexConj K w u

/-- For u in K, u · c(u) = 1 iff ‖σ(u)‖ = 1 for all complex embeddings σ : K → ℂ.
    This characterizes elements of relative norm 1 in K/K⁺. -/
theorem mul_complexConj_eq_one_iff (u : K) :
    u * cmComplexConj K u = 1 ↔
      ∀ (φ : K →+* ℂ), ‖φ u‖ = 1 := by
  constructor
  · intro h φ
    -- φ(u * c(u)) = 1
    have hprod : φ u * φ (cmComplexConj K u) = 1 := by
      rw [← map_mul, h, map_one]
    -- φ(c(u)) = conj(φ(u))
    rw [cmComplexConj_embedding] at hprod
    -- φ(u) * conj(φ(u)) = ‖φ(u)‖² in ℂ
    rw [RCLike.mul_conj] at hprod
    -- So ‖φ(u)‖² = 1 (as real number, via cast)
    have hone : ‖φ u‖ ^ 2 = 1 := by
      have : (‖φ u‖ : ℂ) ^ 2 = 1 := hprod
      exact_mod_cast this
    have hnn : 0 ≤ ‖φ u‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖φ u‖ - 1)]
  · intro h
    -- Pick any embedding φ
    let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    apply φ.injective
    rw [map_mul, cmComplexConj_embedding, RCLike.mul_conj, map_one]
    have := h φ
    push_cast [this]
    norm_num

/-- Equivalent formulation: u · c(u) = 1 iff all infinite places of K equal 1 at u. -/
theorem mul_complexConj_eq_one_iff_infinitePlace (u : K) :
    u * cmComplexConj K u = 1 ↔
      ∀ (w : InfinitePlace K), w u = 1 := by
  rw [mul_complexConj_eq_one_iff K u, eq_iff_eq u 1]

end UnitDistance.NumberTheory
