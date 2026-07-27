/-
Solution — Block C1 / C1' (sectors, statics, meter) and calibration
theorems. Statements are verbatim restatements of the frozen claims in
`Realization/Challenge.lean` (namespace `Realization.Solution`).
Prover attribution per theorem is logged in REGISTRY.jsonl.
-/
import Realization.Challenge

open Matrix BigOperators

noncomputable section
namespace Realization
namespace Solution

variable {𝕜 : Type*} [Field 𝕜]

/-- Aristotle (project 86cd2325); faithfulness audit passed. -/
theorem skew_symmetric_trace_zero {n : ℕ} [NeZero (2 : 𝕜)]
    (S H : Matrix (Fin n) (Fin n) 𝕜) (hS : Sᵀ = -S) (hH : Hᵀ = H) :
    (S * H).trace = 0 := by
  have hneg : (S * H).trace = -(S * H).trace := by
    calc
      (S * H).trace = (S * H)ᵀ.trace := (Matrix.trace_transpose (S * H)).symm
      _ = (Hᵀ * Sᵀ).trace := by rw [Matrix.transpose_mul]
      _ = (H * (-S)).trace := by rw [hH, hS]
      _ = (-(H * S)).trace := by rw [Matrix.mul_neg]
      _ = -(H * S).trace := Matrix.trace_neg (H * S)
      _ = -(S * H).trace := by rw [Matrix.trace_mul_comm H S]
  have htwo : (2 : 𝕜) * (S * H).trace = 0 := by
    rw [two_mul]
    exact eq_neg_iff_add_eq_zero.mp hneg
  exact (mul_eq_zero.mp htwo).resolve_left (NeZero.ne (2 : 𝕜))

/-- Aristotle (project b52d18ce); faithfulness audit passed. -/
theorem transfer_defect_first_order {A₁ A₂ : Type*} [Ring A₁] [Ring A₂]
    (Φ₀ ψ : A₁ →+ A₂) (hΦ₀ : ∀ a b, Φ₀ (a * b) = Φ₀ a * Φ₀ b) (a b : A₁) :
    (Φ₀ + ψ) (a * b) - (Φ₀ + ψ) a * (Φ₀ + ψ) b
      = (ψ (a * b) - ψ a * Φ₀ b - Φ₀ a * ψ b) - ψ a * ψ b := by
  simp only [AddMonoidHom.add_apply, hΦ₀]
  noncomm_ring

end Solution
end Realization
