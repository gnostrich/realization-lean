/-
Solution — Block C3 (regression locks): the graveyard, machine-checked.
Statements are verbatim restatements of the frozen claims. Prover
attribution per theorem is logged in REGISTRY.jsonl.
-/
import Realization.Challenge

open Matrix BigOperators

noncomputable section
namespace Realization
namespace Solution

variable {𝕜 : Type*} [Field 𝕜]

/-- Aristotle (project 42169a06); faithfulness audit passed. -/
lemma diag_mul_of_blockTriangular {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) :
    (A * B).diag = A.diag * B.diag := by
  funext i
  rw [Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hjlt | hjgt
    · rw [hA hjlt]
      simp
    · rw [hB hjgt]
      simp
  · simp

lemma pow_blockTriangular {n : ℕ}
    {T : Matrix (Fin n) (Fin n) 𝕜} (hT : T.BlockTriangular id) (k : ℕ) :
    (T ^ k).BlockTriangular id := by
  induction k with
  | zero => simp [Matrix.blockTriangular_one]
  | succ k ih =>
      rw [pow_succ]
      exact ih.mul hT

theorem schur_flag_gaming {n : ℕ} (T : Matrix (Fin n) (Fin n) 𝕜)
    (hT : T.BlockTriangular id) (k : ℕ) :
    (T ^ k).diag = (T.diag) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      rw [diag_mul_of_blockTriangular (pow_blockTriangular hT k) hT]
      rw [ih]

/-- Aristotle (project 745b1c04); faithfulness audit passed. -/
theorem no_cost_floor :
    ∃ T : Matrix (Fin 2) (Fin 2) ℂ, T * Tᴴ ≠ Tᴴ * T ∧
      mcMillan (fun k => (Matrix.of ![![(T ^ k).diag 0]]) : Behavior 1 1 ℂ)
        ≤ (1 : ℕ∞) := by
  let T : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
  refine ⟨T, ?_, ?_⟩
  · intro h
    have h00 := congr_fun₂ h (0 : Fin 2) (0 : Fin 2)
    norm_num [T, Matrix.mul_apply, Matrix.conjTranspose_apply] at h00
  · apply sInf_le
    refine ⟨1, rfl, ?_⟩
    let R : Real 1 1 1 ℂ :=
      { A := 0
        B := 1
        C := 1 }
    refine ⟨R, ?_⟩
    funext k i j
    fin_cases i
    fin_cases j
    cases k with
    | zero => simp [Real.behavior, R, T]
    | succ k =>
      have hpow : (T ^ (Nat.succ k)).diag 0 = 0 := by
        cases k with
        | zero => norm_num [T]
        | succ k =>
          have hT : T ^ 2 = 0 := by
            ext i j
            fin_cases i <;> fin_cases j <;>
              norm_num [T, pow_two, Matrix.mul_apply]
          rw [show Nat.succ (Nat.succ k) = 2 + k by omega, pow_add, hT]
          simp
      simpa [Real.behavior, R, Nat.succ_eq_add_one] using hpow.symm

end Solution
end Realization
