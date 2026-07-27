/-
Copyright (c) 2026 realization-lean contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.

# Kronecker realizability

An interface behavior `h : ℕ → K` is realizable by a `d`-dimensional linear
state machine `(A, B, C)` exactly when its Hankel row space is
finite-dimensional of dimension at most `d`.

Both directions are constructive in content:

* realizable → finite rank: the shifts of `h` all lie in the range of the
  observation map of the realization, a space of dimension at most `d`;
* finite rank → realizable: the Hankel row space itself, with the shift
  operator, the vector `h` and evaluation at `0`, is a realization; it is
  transported into `Fin d → K` along any linear embedding (which exists
  because its dimension is at most `d`).
-/
import RealizationLean.Defs

open scoped Matrix

namespace RealizationLean

variable {K : Type*} [Field K]

/-! ## The shift operator on sequences -/

/-- The left shift operator on sequences. -/
def shiftOp : (ℕ → K) →ₗ[K] (ℕ → K) where
  toFun u := fun j => u (j + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem shiftOp_apply (u : ℕ → K) (j : ℕ) : shiftOp u j = u (j + 1) := rfl

theorem shiftOp_shift (h : ℕ → K) (i : ℕ) : shiftOp (shift h i) = shift h (i + 1) := by
  funext j
  simp only [shiftOp_apply, shift_apply]
  congr 1
  omega

theorem shiftOp_mem_hankelSpace (h : ℕ → K) {u : ℕ → K} (hu : u ∈ hankelSpace h) :
    shiftOp u ∈ hankelSpace h := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [shiftOp_shift]
      exact shift_mem_hankelSpace h (i + 1)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- The shift operator restricted to the Hankel row space: the internal
dynamics of the canonical realization. -/
def hankelShift (h : ℕ → K) : hankelSpace h →ₗ[K] hankelSpace h :=
  shiftOp.restrict fun _ hu => shiftOp_mem_hankelSpace h hu

@[simp] theorem hankelShift_coe (h : ℕ → K) (u : hankelSpace h) :
    ((hankelShift h u : hankelSpace h) : ℕ → K) = shiftOp (u : ℕ → K) := rfl

/-- The canonical state of `h`: the sequence itself, sitting in its own Hankel
row space. -/
def hankelState (h : ℕ → K) : hankelSpace h :=
  ⟨h, by simpa using shift_mem_hankelSpace h 0⟩

theorem hankelShift_pow_state (h : ℕ → K) (k : ℕ) :
    (((hankelShift h) ^ k) (hankelState h) : ℕ → K) = shift h k := by
  induction k with
  | zero => simp [hankelState]
  | succ k ih =>
      rw [pow_succ']
      show ((hankelShift h) ((hankelShift h ^ k) (hankelState h)) : ℕ → K) = _
      rw [hankelShift_coe, ih, shiftOp_shift]

/-! ## Realizable → finite Hankel rank -/

theorem hankelSpace_le_range_obs {d : ℕ} (h : ℕ → K) (A : Matrix (Fin d) (Fin d) K)
    (B C : Fin d → K) (hr : Realizes h A B C) :
    hankelSpace h ≤ LinearMap.range (obs A C) := by
  rw [hankelSpace, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine ⟨A ^ i *ᵥ B, ?_⟩
  funext j
  simp only [obs_apply, shift_apply, Matrix.mulVec_mulVec, ← pow_add]
  rw [hr (i + j), Nat.add_comm j i]

theorem finite_and_finrank_le_of_realizable {d : ℕ} (h : ℕ → K) (hd : IsRealizable h d) :
    Module.Finite K (hankelSpace h) ∧ Module.finrank K (hankelSpace h) ≤ d := by
  obtain ⟨A, B, C, hr⟩ := hd
  have hle := hankelSpace_le_range_obs h A B C hr
  haveI : FiniteDimensional K (LinearMap.range (obs A C)) := inferInstance
  haveI : FiniteDimensional K (hankelSpace h) := Submodule.finiteDimensional_of_le hle
  refine ⟨inferInstance, ?_⟩
  calc Module.finrank K (hankelSpace h)
      ≤ Module.finrank K (LinearMap.range (obs A C)) := Submodule.finrank_mono hle
    _ ≤ Module.finrank K (Fin d → K) := LinearMap.finrank_range_le _
    _ = d := Module.finrank_fin_fun K

/-! ## Finite Hankel rank → realizable

The transport of the canonical realization into `Fin d → K`. -/

/-- Extension by zero `(Fin r → K) →ₗ[K] (Fin d → K)`, for `r ≤ d`. -/
def pad (r d : ℕ) : (Fin r → K) →ₗ[K] (Fin d → K) where
  toFun v i := if hi : (i : ℕ) < r then v ⟨i, hi⟩ else 0
  map_add' u v := by funext i; by_cases hi : (i : ℕ) < r <;> simp [hi]
  map_smul' c v := by funext i; by_cases hi : (i : ℕ) < r <;> simp [hi]

theorem pad_injective {r d : ℕ} (hrd : r ≤ d) :
    Function.Injective (pad (K := K) r d) := by
  intro u v huv
  funext j
  have hj : (j : ℕ) < d := lt_of_lt_of_le j.2 hrd
  have := congrFun huv ⟨(j : ℕ), hj⟩
  simpa [pad, j.2] using this

/-- A linear functional on `Fin d → K` is the dot product with its vector of
values on the standard basis. -/
theorem dotProduct_coeffs (d : ℕ) (φ : (Fin d → K) →ₗ[K] K) (x : Fin d → K) :
    (fun i => φ (Pi.single i 1)) ⬝ᵥ x = φ x := by
  have hx : x = ∑ i, x i • Pi.single i (1 : K) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  rw [map_sum, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_comm]

theorem realizable_of_finite_of_finrank_le {d : ℕ} (h : ℕ → K)
    (hfin : Module.Finite K (hankelSpace h)) (hd : Module.finrank K (hankelSpace h) ≤ d) :
    IsRealizable h d := by
  haveI := hfin
  set V := hankelSpace h with hV
  set r := Module.finrank K V with hr
  -- an embedding of the Hankel row space into `Fin d → K`, with a retraction
  let bV : Module.Basis (Fin r) K V := Module.finBasis K V
  let ι : V →ₗ[K] (Fin d → K) := (pad r d).comp bV.equivFun.toLinearMap
  have hιinj : Function.Injective ι :=
    (pad_injective hd).comp bV.equivFun.injective
  obtain ⟨π, hπ⟩ :=
    ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hιinj)
  have hπι : ∀ v : V, π (ι v) = v := fun v => congrArg (fun f => f v) hπ
  -- the transported dynamics, input port and output port
  let F : (Fin d → K) →ₗ[K] (Fin d → K) := ι.comp ((hankelShift h).comp π)
  let A : Matrix (Fin d) (Fin d) K := LinearMap.toMatrixAlgEquiv' F
  let φ : (Fin d → K) →ₗ[K] K :=
    { toFun := fun x => ((π x : V) : ℕ → K) 0
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp }
  refine ⟨A, ι (hankelState h), fun i => φ (Pi.single i 1), ?_⟩
  intro k
  -- `A ^ k` acts as `F ^ k`
  have hA : ∀ x : Fin d → K, A ^ k *ᵥ x = (F ^ k) x := by
    intro x
    have : Matrix.toLinAlgEquiv' (A ^ k) = F ^ k := by
      rw [map_pow]
      congr 1
      exact AlgEquiv.symm_apply_apply _ _
    rw [← Matrix.toLinAlgEquiv'_apply, this]
  -- `F` intertwines the canonical dynamics along `ι`
  have hFι : ∀ (j : ℕ) (v : V), (F ^ j) (ι v) = ι (((hankelShift h) ^ j) v) := by
    intro j
    induction j with
    | zero => intro v; simp
    | succ j ih =>
        intro v
        rw [pow_succ', pow_succ']
        show F ((F ^ j) (ι v)) = _
        rw [ih v]
        show ι ((hankelShift h) (π (ι (((hankelShift h) ^ j) v)))) = _
        rw [hπι]
        rfl
  rw [hA, hFι k (hankelState h), dotProduct_coeffs]
  show h k = ((π (ι (((hankelShift h) ^ k) (hankelState h))) : V) : ℕ → K) 0
  rw [hπι, hankelShift_pow_state]
  simp

/-! ## The headline -/

/-- **Kronecker realizability.** -/
theorem kronecker_realizable_iff (h : ℕ → K) (d : ℕ) :
    IsRealizable h d ↔
      Module.Finite K (hankelSpace h) ∧ Module.finrank K (hankelSpace h) ≤ d :=
  ⟨finite_and_finrank_le_of_realizable h,
   fun ⟨hfin, hd⟩ => realizable_of_finite_of_finrank_le h hfin hd⟩

end RealizationLean
