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

/-- Aristotle (project 98ac002c); faithfulness audit passed. -/
theorem skew_quadratic_null {n : ℕ} [NeZero (2 : 𝕜)]
    (S : Matrix (Fin n) (Fin n) 𝕜) (hS : Sᵀ = -S) (x : Fin n → 𝕜) :
    x ⬝ᵥ S.mulVec x = 0 := by
  have hneg : x ⬝ᵥ S.mulVec x = -(x ⬝ᵥ S.mulVec x) := by
    calc
      x ⬝ᵥ S.mulVec x = (x ᵥ* S) ⬝ᵥ x := Matrix.dotProduct_mulVec x S x
      _ = (Sᵀ *ᵥ x) ⬝ᵥ x := by rw [Matrix.mulVec_transpose]
      _ = x ⬝ᵥ (Sᵀ *ᵥ x) := dotProduct_comm _ _
      _ = x ⬝ᵥ ((-S) *ᵥ x) := by rw [hS]
      _ = -(x ⬝ᵥ S.mulVec x) := by
        rw [Matrix.neg_mulVec, dotProduct_neg]
  have htwo : (2 : 𝕜) * (x ⬝ᵥ S.mulVec x) = 0 := by
    calc
      (2 : 𝕜) * (x ⬝ᵥ S.mulVec x) =
          (x ⬝ᵥ S.mulVec x) + (x ⬝ᵥ S.mulVec x) := two_mul _
      _ = -(x ⬝ᵥ S.mulVec x) + (x ⬝ᵥ S.mulVec x) :=
        congrArg (fun z => z + (x ⬝ᵥ S.mulVec x)) hneg
      _ = 0 := neg_add_cancel _
  exact (mul_eq_zero.mp htwo).resolve_left (NeZero.ne (2 : 𝕜))

/-- Aristotle (project ad7010d2); faithfulness audit passed. -/
theorem sym_skew_unique_decomposition {n : ℕ} [NeZero (2 : 𝕜)]
    (A : Matrix (Fin n) (Fin n) 𝕜) :
    (∃! P : Matrix (Fin n) (Fin n) 𝕜 × Matrix (Fin n) (Fin n) 𝕜,
      P.1ᵀ = P.1 ∧ P.2ᵀ = -P.2 ∧ A = P.1 + P.2) ∧
    (∀ S : Matrix (Fin n) (Fin n) 𝕜, Sᵀ = S → Sᵀ = -S → S = 0) := by
  have htwo : (2 : 𝕜) ≠ 0 := NeZero.ne 2
  let X : Matrix (Fin n) (Fin n) 𝕜 := fun i j => (A i j + A j i) / 2
  let Y : Matrix (Fin n) (Fin n) 𝕜 := fun i j => (A i j - A j i) / 2
  constructor
  · refine ⟨(X, Y), ?_, ?_⟩
    · constructor
      · ext i j
        simp [X, Matrix.transpose_apply, add_comm]
      constructor
      · ext i j
        simp [Y, Matrix.transpose_apply]
        ring
      · ext i j
        simp [X, Y]
        field_simp
        ring
    · rintro ⟨U, V⟩ ⟨hU, hV, hA⟩
      apply Prod.ext
      · ext i j
        have hu := congrArg (fun M : Matrix (Fin n) (Fin n) 𝕜 => M j i) hU
        have hv := congrArg (fun M : Matrix (Fin n) (Fin n) 𝕜 => M j i) hV
        have haij := congrArg (fun M : Matrix (Fin n) (Fin n) 𝕜 => M i j) hA
        have haji := congrArg (fun M : Matrix (Fin n) (Fin n) 𝕜 => M j i) hA
        simp [Matrix.transpose_apply] at hu hv haij haji
        simp [X]
        apply (eq_div_iff htwo).2
        have hv' : V j i = -V i j := by linear_combination hv
        rw [haij, haji, ← hu, hv']
        ring
      · ext i j
        have hu := congrArg (fun M : Matrix (Fin n) (Fin n) 𝕜 => M j i) hU
        have hv := congrArg (fun M : Matrix (Fin n) (Fin n) 𝕜 => M j i) hV
        have haij := congrArg (fun M : Matrix (Fin n) (Fin n) 𝕜 => M i j) hA
        have haji := congrArg (fun M : Matrix (Fin n) (Fin n) 𝕜 => M j i) hA
        simp [Matrix.transpose_apply] at hu hv haij haji
        simp [Y]
        apply (eq_div_iff htwo).2
        have hv' : V j i = -V i j := by linear_combination hv
        rw [haij, haji, ← hu, hv']
        ring
  · intro S hS hSneg
    ext i j
    have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) 𝕜 => M j i) hS
    have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) 𝕜 => M j i) hSneg
    simp [Matrix.transpose_apply] at h1 h2
    have hz : (2 : 𝕜) * S i j = 0 := by
      linear_combination h1 + h2
    exact (mul_eq_zero.mp hz).resolve_left htwo

/-- Aristotle (project a846b9bc); faithfulness audit passed. -/
theorem tilt_displaces_uniquely {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : K.PosDef) (b t : Fin n → ℝ) :
    (∃! s, K.mulVec s = b) ∧
    (∀ s₀ s₁, K.mulVec s₀ = b → K.mulVec s₁ = b + t →
      s₁ = s₀ + K⁻¹.mulVec t) := by
  have hunit : IsUnit K := hK.isUnit
  have hdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hunit
  have hright : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv K hdet
  have hinj : Function.Injective K.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  constructor
  · refine ⟨K⁻¹ *ᵥ b, ?_, ?_⟩
    · change K *ᵥ (K⁻¹ *ᵥ b) = b
      rw [Matrix.mulVec_mulVec, hright, Matrix.one_mulVec]
    · intro y hy
      apply hinj
      rw [hy, Matrix.mulVec_mulVec, hright, Matrix.one_mulVec]
  · intro s₀ s₁ hs₀ hs₁
    apply hinj
    rw [hs₁, Matrix.mulVec_add, hs₀, Matrix.mulVec_mulVec, hright,
      Matrix.one_mulVec]

/-- Aristotle (project d62e2fde); faithfulness audit passed. -/
lemma symmetric_mulVec_dotProduct {n : ℕ}
    (H : Matrix (Fin n) (Fin n) 𝕜) (hH : Hᵀ = H)
    (u v : Fin n → 𝕜) :
    u ⬝ᵥ H.mulVec v = v ⬝ᵥ H.mulVec u := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm]
  -- Goal: ∑ x, ∑ x_1, H x x_1 * (u x * v x_1) = ∑ x, ∑ x_1, H x x_1 * (u x_1 * v x)
  rw [Finset.sum_comm]
  -- Now we need to show ∑ x_1, ∑ x, H x x_1 * (u x * v x_1) = ∑ x, ∑ x_1, H x x_1 * (u x_1 * v x)
  congr 1
  ext i
  congr 1
  ext j
  have hsym : H j i = H i j := by simpa using (congrFun (congrFun hH j) i).symm
  rw [hsym]

lemma symmetric_edge_difference {n : ℕ}
    (H : Matrix (Fin n) (Fin n) 𝕜) (hH : Hᵀ = H)
    (u v : Fin n → 𝕜) :
    (u + v) ⬝ᵥ H.mulVec (v - u) =
      v ⬝ᵥ H.mulVec v - u ⬝ᵥ H.mulVec u := by
  simp only [add_dotProduct, Matrix.mulVec_sub, dotProduct_sub]
  rw [symmetric_mulVec_dotProduct H hH u v]
  ring

lemma sum_succ_sub_castSucc {m : ℕ} (f : Fin (m + 1) → 𝕜) :
    ∑ i : Fin m, (f i.succ - f i.castSucc) = f (Fin.last m) - f 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Fin.sum_univ_castSucc]
    have ih' := ih (fun i => f i.castSucc)
    simp_all

theorem symmetric_loop_work_zero {n m : ℕ} [NeZero (2 : 𝕜)]
    (H : Matrix (Fin n) (Fin n) 𝕜) (hH : Hᵀ = H)
    (x : Fin (m + 1) → Fin n → 𝕜) (hclosed : x (Fin.last m) = x 0) :
    ∑ i : Fin m, (2⁻¹ : 𝕜) •
      ((x i.castSucc + x i.succ) ⬝ᵥ H.mulVec (x i.succ - x i.castSucc)) = 0 := by
  simp_rw [symmetric_edge_difference H hH]
  rw [← Finset.smul_sum]
  have ht := sum_succ_sub_castSucc (fun j => x j ⬝ᵥ H.mulVec (x j))
  rw [ht, hclosed, sub_self, smul_zero]

end Solution
end Realization
