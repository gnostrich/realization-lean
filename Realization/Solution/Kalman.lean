/-
Solution — Kalman uniqueness: minimal realizations are similar (gauge).
The observability map of a minimal realization is injective with image
the state space; composing the two gives the similarity.
Aristotle (project d9abbcd9); faithfulness audit passed.
-/
import Realization.Solution.Kronecker

open Matrix BigOperators Module

set_option linter.unusedSectionVars false

noncomputable section
namespace Realization
namespace Solution

variable {𝕜 : Type*} [Field 𝕜] {p m : ℕ}

def observabilityMap {p m d : ℕ} (R : Real p m d 𝕜) :
    (Fin d → 𝕜) →ₗ[𝕜] Germ p 𝕜 where
  toFun x i := R.C *ᵥ (R.A ^ i *ᵥ x)
  map_add' x y := by
    ext i a
    simp [Matrix.mulVec_add]
  map_smul' c x := by
    ext i a
    simp [Matrix.mulVec_smul]

lemma colGerm_eq_observabilityMap {p m d : ℕ} {g : Behavior p m 𝕜}
    (R : Real p m d 𝕜) (h : Realizes R g) (j : ℕ) (b : Fin m) :
    colGerm g j b = observabilityMap R (R.A ^ j *ᵥ R.B *ᵥ Pi.single b 1) := by
  ext i a
  rw [h.symm] at *
  simp [colGerm, observabilityMap]
  rw [Real.behavior]
  rw [pow_add]
  rw [← Matrix.mul_assoc]
  conv_lhs => rw [Matrix.mul_apply]
  rw [Matrix.mulVec, Matrix.col]
  rfl

lemma stateSpace_le_observabilityRange {p m d : ℕ} {g : Behavior p m 𝕜}
    (R : Real p m d 𝕜) (h : Realizes R g) :
    stateSpace g ≤ (observabilityMap R).range := by
  rw [stateSpace]
  apply Submodule.span_le.mpr
  intro y hy
  obtain ⟨⟨j, b⟩, rfl⟩ := hy
  simp only
  rw [colGerm_eq_observabilityMap R h j b]
  exact LinearMap.mem_range_self _ _

lemma observabilityMap_minimal {p m d : ℕ} {g : Behavior p m 𝕜}
    (R : Real p m d 𝕜) (h : Realizes R g)
    (hmin : mcMillan g = (d : ℕ∞)) :
    (observabilityMap R).range = stateSpace g ∧
      Function.Injective (observabilityMap R) := by
  -- Get the finite dimensionality and dimension of stateSpace
  have ⟨hdim, hfinrank⟩ := stateSpace_finrank_of_mcMillan hmin
  -- We have stateSpace ≤ range from stateSpace_le_observabilityRange
  have hle := stateSpace_le_observabilityRange R h
  -- The finrank of the domain (Fin d → 𝕜) is d
  have hdom_dim : Module.finrank 𝕜 (Fin d → 𝕜) = d := by simp
  -- The finrank of range is ≤ finrank of domain
  have hrange_finrank_le : Module.finrank 𝕜 (observabilityMap R).range ≤ d := by
    calc Module.finrank 𝕜 (observabilityMap R).range
        ≤ Module.finrank 𝕜 (Fin d → 𝕜) := LinearMap.finrank_range_le _
      _ = d := hdom_dim
  -- The finrank of stateSpace is d
  have hstate_finrank : Module.finrank 𝕜 (stateSpace g) = d := hfinrank
  -- Since stateSpace ≤ range and stateSpace has dimension d, range has dimension ≥ d
  have hrange_finrank_ge : d ≤ Module.finrank 𝕜 (observabilityMap R).range := by
    calc d = Module.finrank 𝕜 (stateSpace g) := hstate_finrank.symm
      _ ≤ Module.finrank 𝕜 (observabilityMap R).range := Submodule.finrank_mono hle
  -- Therefore range has dimension exactly d
  have hrange_finrank : Module.finrank 𝕜 (observabilityMap R).range = d := le_antisymm hrange_finrank_le hrange_finrank_ge
  -- Since stateSpace ≤ range and both have finrank d, they are equal
  have heq : (observabilityMap R).range = stateSpace g := by
    rw [eq_comm]
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [hrange_finrank, hfinrank]
  -- For injectivity: domain finrank = range finrank implies ker = 0
  have hinj : Function.Injective (observabilityMap R) := by
    have hker_le : Module.finrank 𝕜 (observabilityMap R).range + 
                   Module.finrank 𝕜 (LinearMap.ker (observabilityMap R)) = 
                   Module.finrank 𝕜 (Fin d → 𝕜) := 
      LinearMap.finrank_range_add_finrank_ker (observabilityMap R)
    have hker_eq_zero : Module.finrank 𝕜 (LinearMap.ker (observabilityMap R)) = 0 := by
      rw [hrange_finrank, hdom_dim] at hker_le
      linarith
    have hker_bot : LinearMap.ker (observabilityMap R) = ⊥ := by
      rw [Submodule.finrank_eq_zero] at hker_eq_zero
      exact hker_eq_zero
    exact LinearMap.ker_eq_bot.mp hker_bot
  exact ⟨heq, hinj⟩

lemma observabilityMap_shift {p m d : ℕ} (R : Real p m d 𝕜)
    (x : Fin d → 𝕜) (i : ℕ) :
    observabilityMap R (R.A *ᵥ x) i = observabilityMap R x (i + 1) := by
  simp [observabilityMap, Matrix.mulVec_mulVec, pow_succ, Matrix.mul_assoc]

lemma observabilityMap_input {p m d : ℕ} {g : Behavior p m 𝕜}
    (R : Real p m d 𝕜) (h : Realizes R g) (u : Fin m → 𝕜) (i : ℕ) :
    observabilityMap R (R.B *ᵥ u) i = g i *ᵥ u := by
  simp only [observabilityMap, Realizes] at *
  show R.C *ᵥ (R.A ^ i *ᵥ (R.B *ᵥ u)) = g i *ᵥ u
  rw [h.symm, Real.behavior]
  rw [← Matrix.mulVec_mulVec]
  rw [← Matrix.mulVec_mulVec]

lemma minimal_realizations_linearEquiv {p m d : ℕ} (g : Behavior p m 𝕜)
    (R₁ R₂ : Real p m d 𝕜) (h₁ : Realizes R₁ g) (h₂ : Realizes R₂ g)
    (hmin : mcMillan g = (d : ℕ∞)) :
    ∃ e : (Fin d → 𝕜) ≃ₗ[𝕜] (Fin d → 𝕜),
      (∀ x, e (R₁.A *ᵥ x) = R₂.A *ᵥ e x) ∧
      (∀ u, e (R₁.B *ᵥ u) = R₂.B *ᵥ u) ∧
      (∀ x, R₁.C *ᵥ x = R₂.C *ᵥ e x) := by
  obtain ⟨hr₁, hinj₁⟩ := observabilityMap_minimal R₁ h₁ hmin
  obtain ⟨hr₂, hinj₂⟩ := observabilityMap_minimal R₂ h₂ hmin
  let e₁ := (LinearEquiv.ofInjective (observabilityMap R₁) hinj₁).trans
    (LinearEquiv.ofEq _ _ hr₁)
  let e₂ := (LinearEquiv.ofInjective (observabilityMap R₂) hinj₂).trans
    (LinearEquiv.ofEq _ _ hr₂)
  let e := e₁.trans e₂.symm
  have key (x : Fin d → 𝕜) : observabilityMap R₂ (e x) = observabilityMap R₁ x := by
    have h := e₂.apply_symm_apply (e₁ x)
    exact congrArg Subtype.val h
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x
    apply hinj₂
    ext i
    rw [key, observabilityMap_shift, observabilityMap_shift]
    exact congrFun (congrFun (key x).symm (i + 1)) _
  · intro u
    apply hinj₂
    ext i
    rw [key, observabilityMap_input R₁ h₁, observabilityMap_input R₂ h₂]
  · intro x
    have h := congrFun (key x) 0
    simpa [observabilityMap] using h.symm

theorem kalman_uniqueness {p m d : ℕ} (g : Behavior p m 𝕜)
    (R₁ R₂ : Real p m d 𝕜) (h₁ : Realizes R₁ g) (h₂ : Realizes R₂ g)
    (hmin : mcMillan g = (d : ℕ∞)) :
    ∃ S : Matrix (Fin d) (Fin d) 𝕜, IsUnit S ∧
      R₂.A = S * R₁.A * S⁻¹ ∧ R₂.B = S * R₁.B ∧ R₂.C = R₁.C * S⁻¹ := by
  obtain ⟨e, hA, hB, hC⟩ := minimal_realizations_linearEquiv g R₁ R₂ h₁ h₂ hmin
  let S : Matrix (Fin d) (Fin d) 𝕜 := LinearMap.toMatrix' e.toLinearMap
  let T : Matrix (Fin d) (Fin d) 𝕜 := LinearMap.toMatrix' e.symm.toLinearMap
  have hS (x : Fin d → 𝕜) : S *ᵥ x = e x := by
    change Matrix.toLin' S x = e x
    simp [S]
  have hT (x : Fin d → 𝕜) : T *ᵥ x = e.symm x := by
    change Matrix.toLin' T x = e.symm x
    simp [T]
  have hST : S * T = 1 := by
    apply Matrix.mulVec_injective
    funext x
    rw [← Matrix.mulVec_mulVec]
    simp [hS, hT]
  have hTS : T * S = 1 := by
    apply Matrix.mulVec_injective
    funext x
    rw [← Matrix.mulVec_mulVec]
    simp [hS, hT]
  have hunit : IsUnit S := IsUnit.of_mul_eq_one T hST
  have hinv : S⁻¹ = T := Matrix.inv_eq_right_inv hST
  have hAmat : S * R₁.A = R₂.A * S := by
    apply Matrix.mulVec_injective
    funext x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp only [hS]
    exact hA x
  have hBmat : S * R₁.B = R₂.B := by
    apply Matrix.mulVec_injective
    funext u
    rw [← Matrix.mulVec_mulVec]
    rw [hS]
    exact hB u
  have hCmat : R₁.C = R₂.C * S := by
    apply Matrix.mulVec_injective
    funext x
    rw [← Matrix.mulVec_mulVec]
    rw [hS]
    exact hC x
  refine ⟨S, hunit, ?_, ?_, ?_⟩
  · rw [hinv]
    calc
      R₂.A = R₂.A * 1 := by rw [Matrix.mul_one]
      _ = R₂.A * (S * T) := by rw [hST]
      _ = (R₂.A * S) * T := by rw [Matrix.mul_assoc]
      _ = (S * R₁.A) * T := by rw [hAmat]
  · exact hBmat.symm
  · rw [hinv]
    calc
      R₂.C = R₂.C * (1 : Matrix (Fin d) (Fin d) 𝕜) := by rw [Matrix.mul_one]
      _ = R₂.C * (S * T) := by rw [hST]
      _ = (R₂.C * S) * T := by rw [Matrix.mul_assoc]
      _ = R₁.C * T := by rw [hCmat]

end Solution
end Realization
