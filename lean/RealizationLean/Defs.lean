/-
Copyright (c) 2026 realization-lean contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.

# Definitions of the realization spine

Interface behaviors (`ℕ → K`), their Hankel row spaces, finite-dimensional
linear realizations `(A, B, C)`, reachability/controllability, the observation
map and the unobservable subspace, and finite mode sums.

Every definition here is inlined verbatim (modulo the namespace prefix) into
the statement registry `Challenge.lean` and the comparator bridge
`Solution.lean`.
-/
import Mathlib

open scoped Matrix

namespace RealizationLean

section Sequences

variable {K : Type*} [Field K]

/-- The `i`-th shift of an interface behavior: `shift h i = fun j => h (i + j)`.
This is exactly row `i` of the infinite Hankel matrix of `h`. -/
def shift (h : ℕ → K) (i : ℕ) : ℕ → K := fun j => h (i + j)

/-- The row space of the infinite Hankel matrix of `h`: the span, inside the
function space `ℕ → K`, of all shifts of `h`. Its dimension is the Hankel rank
of `h`. -/
def hankelSpace (h : ℕ → K) : Submodule K (ℕ → K) :=
  Submodule.span K (Set.range (shift h))

/-- The span of the first `n` shifts of `h` — the `n`-th stage of the finite
test. -/
def shiftSpan (h : ℕ → K) (n : ℕ) : Submodule K (ℕ → K) :=
  Submodule.span K (shift h '' Set.Iio n)

/-- `(A, B, C)` realizes the interface behavior `h`: every Markov parameter of
the state machine is the corresponding value of `h`. -/
def Realizes {d : ℕ} (h : ℕ → K) (A : Matrix (Fin d) (Fin d) K) (B C : Fin d → K) : Prop :=
  ∀ k : ℕ, h k = C ⬝ᵥ (A ^ k *ᵥ B)

/-- `h` is realizable in dimension `d`: some `d`-dimensional state machine
produces it. -/
def IsRealizable (h : ℕ → K) (d : ℕ) : Prop :=
  ∃ (A : Matrix (Fin d) (Fin d) K) (B C : Fin d → K), Realizes h A B C

/-- The reachable subspace of `(A, B)`. -/
def reachable {d : ℕ} (A : Matrix (Fin d) (Fin d) K) (B : Fin d → K) :
    Submodule K (Fin d → K) :=
  Submodule.span K (Set.range fun k : ℕ => A ^ k *ᵥ B)

/-- `(A, B)` is controllable: every internal state is reachable from the input
port. -/
def Controllable {d : ℕ} (A : Matrix (Fin d) (Fin d) K) (B : Fin d → K) : Prop :=
  reachable A B = ⊤

/-- The observation map of `(A, C)`: the interface trace of an internal state. -/
def obs {d : ℕ} (A : Matrix (Fin d) (Fin d) K) (C : Fin d → K) :
    (Fin d → K) →ₗ[K] (ℕ → K) where
  toFun x := fun k => C ⬝ᵥ (A ^ k *ᵥ x)
  map_add' x y := by
    funext k
    simp [Matrix.mulVec_add, dotProduct_add]
  map_smul' r x := by
    funext k
    simp [Matrix.mulVec_smul, dotProduct_smul]

/-- The unobservable subspace: internal states with identically zero interface
trace. This is what "never reaches the interface" means. -/
def unobservable {d : ℕ} (A : Matrix (Fin d) (Fin d) K) (C : Fin d → K) :
    Submodule K (Fin d → K) :=
  LinearMap.ker (obs A C)

/-- `(A, C)` is observable: no internal state is invisible at the interface. -/
def Observable {d : ℕ} (A : Matrix (Fin d) (Fin d) K) (C : Fin d → K) : Prop :=
  unobservable A C = ⊥

/-- A finite sum of geometric modes: `n ↦ ∑ p ∈ s, c p * p ^ n`. The elements
of `s` are the poles (inverse poles of the generating function) and `c p` is
the residue at `p`. -/
def modeSum (s : Finset K) (c : K → K) : ℕ → K := fun n => ∑ p ∈ s, c p * p ^ n

end Sequences

/-- The quadratic form `xᵀ M x`; over ℝ, the "work" of the field `M` along
`x`. -/
def quadForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * M i j * x j

/-! ## Basic API -/

section Sequences

variable {K : Type*} [Field K]

@[simp] theorem shift_apply (h : ℕ → K) (i j : ℕ) : shift h i j = h (i + j) := rfl

@[simp] theorem shift_zero (h : ℕ → K) : shift h 0 = h := by
  funext j; simp [shift]

@[simp] theorem obs_apply {d : ℕ} (A : Matrix (Fin d) (Fin d) K) (C : Fin d → K)
    (x : Fin d → K) (k : ℕ) : obs A C x k = C ⬝ᵥ (A ^ k *ᵥ x) := rfl

theorem mem_unobservable_iff {d : ℕ} {A : Matrix (Fin d) (Fin d) K} {C : Fin d → K}
    {x : Fin d → K} : x ∈ unobservable A C ↔ ∀ k : ℕ, C ⬝ᵥ (A ^ k *ᵥ x) = 0 := by
  simp [unobservable, LinearMap.mem_ker, funext_iff]

theorem shiftSpan_le_hankelSpace (h : ℕ → K) (n : ℕ) : shiftSpan h n ≤ hankelSpace h :=
  Submodule.span_mono (by rintro _ ⟨i, -, rfl⟩; exact ⟨i, rfl⟩)

theorem shiftSpan_mono (h : ℕ → K) {m n : ℕ} (hmn : m ≤ n) :
    shiftSpan h m ≤ shiftSpan h n :=
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi hmn)

theorem shift_mem_shiftSpan (h : ℕ → K) {i n : ℕ} (hi : i < n) :
    shift h i ∈ shiftSpan h n :=
  Submodule.subset_span ⟨i, hi, rfl⟩

theorem shift_mem_hankelSpace (h : ℕ → K) (i : ℕ) : shift h i ∈ hankelSpace h :=
  Submodule.subset_span ⟨i, rfl⟩

end Sequences

end RealizationLean
