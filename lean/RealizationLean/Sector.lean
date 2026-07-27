/-
Copyright (c) 2026 realization-lean contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.

# Sector decomposition and loop-work nullity

Every square real matrix splits uniquely as symmetric ⊕ skew, and the skew
sector does no work: its quadratic form vanishes identically.
-/
import RealizationLean.Defs

open scoped Matrix

namespace RealizationLean

variable {n : ℕ}

/-- The symmetric sector of `M`. -/
noncomputable def symmPart (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (2 : ℝ)⁻¹ • (M + Mᵀ)

/-- The skew sector of `M`. -/
noncomputable def skewPart (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (2 : ℝ)⁻¹ • (M - Mᵀ)

theorem symmPart_isSymm (M : Matrix (Fin n) (Fin n) ℝ) : (symmPart M)ᵀ = symmPart M := by
  simp [symmPart, Matrix.transpose_add, add_comm]

theorem skewPart_isSkew (M : Matrix (Fin n) (Fin n) ℝ) : (skewPart M)ᵀ = -skewPart M := by
  simp [skewPart, Matrix.transpose_sub, ← smul_neg, neg_sub]

theorem symmPart_add_skewPart (M : Matrix (Fin n) (Fin n) ℝ) :
    M = symmPart M + skewPart M := by
  ext i j
  simp [symmPart, skewPart, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.transpose_apply]
  ring

/-- **Unique symmetric ⊕ skew decomposition.** -/
theorem sector_decomposition (M : Matrix (Fin n) (Fin n) ℝ) :
    ∃! P : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ,
      P.1ᵀ = P.1 ∧ P.2ᵀ = -P.2 ∧ M = P.1 + P.2 := by
  refine ⟨(symmPart M, skewPart M),
    ⟨symmPart_isSymm M, skewPart_isSkew M, symmPart_add_skewPart M⟩, ?_⟩
  rintro ⟨S, W⟩ ⟨hS, hW, hM⟩
  dsimp only at hS hW hM
  have hS2 : M + Mᵀ = (2 : ℝ) • S := by
    rw [hM, Matrix.transpose_add, hS, hW]
    ext i j
    simp [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply]
    ring
  have hW2 : M - Mᵀ = (2 : ℝ) • W := by
    rw [hM, Matrix.transpose_add, hS, hW]
    ext i j
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply]
    ring
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  refine Prod.ext ?_ ?_
  · show S = symmPart M
    rw [symmPart, hS2, smul_smul, inv_mul_cancel₀ h2, one_smul]
  · show W = skewPart M
    rw [skewPart, hW2, smul_smul, inv_mul_cancel₀ h2, one_smul]

/-- **Loop-work nullity.** The skew sector does no work. -/
theorem loop_work_nullity (W : Matrix (Fin n) (Fin n) ℝ) (hW : Wᵀ = -W) (x : Fin n → ℝ) :
    quadForm W x = 0 := by
  have hskew : ∀ i j, W j i = -W i j := by
    intro i j
    have h := congrFun (congrFun hW i) j
    simpa [Matrix.transpose_apply, Matrix.neg_apply] using h
  have h1 : quadForm W x = ∑ i, ∑ j, x j * W j i * x i := by
    simp only [quadForm]
    exact Finset.sum_comm
  have h2 : quadForm W x + quadForm W x = 0 := by
    nth_rewrite 2 [h1]
    simp only [quadForm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hskew j i]
    ring
  linarith

end RealizationLean
