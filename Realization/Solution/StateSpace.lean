/-
Solution — the state-space (shift-realization) framework.

For a behavior `g`, the *state space* is the span of all shifted column
germs `i ↦ g (i + j) · e_b` inside the function space `ℕ → Fin p → 𝕜`.
It is shift-invariant; its dimension is the McMillan degree; truncation
to a window of length `n` has image the column space of `hankel g n`.
This single object yields Kronecker realizability (both directions),
rank stabilization at the degree, and (downstream) Kalman uniqueness.
-/
import Realization.Solution.Basic

open Matrix BigOperators Module

set_option linter.unusedSectionVars false

noncomputable section
namespace Realization
namespace Solution

variable {𝕜 : Type*} [Field 𝕜] {p m : ℕ}

/-- The ambient space of output germs. -/
abbrev Germ (p : ℕ) (𝕜 : Type*) := ℕ → Fin p → 𝕜

/-- The `(j,b)`-th shifted column germ of a behavior. -/
def colGerm (g : Behavior p m 𝕜) (j : ℕ) (b : Fin m) : Germ p 𝕜 :=
  fun i a => g (i + j) a b

/-- The state space of a behavior: span of all shifted column germs. -/
def stateSpace (g : Behavior p m 𝕜) : Submodule 𝕜 (Germ p 𝕜) :=
  Submodule.span 𝕜
    (Set.range fun jb : ℕ × Fin m => colGerm g jb.1 jb.2)

/-- Truncated state space: only the first `N` shifts. -/
def stateSpaceUpTo (g : Behavior p m 𝕜) (N : ℕ) : Submodule 𝕜 (Germ p 𝕜) :=
  Submodule.span 𝕜
    (Set.range fun jb : Fin N × Fin m => colGerm g jb.1 jb.2)

/-- The left-shift operator on germs. -/
def shiftL (p : ℕ) (𝕜 : Type*) [Field 𝕜] : Germ p 𝕜 →ₗ[𝕜] Germ p 𝕜 where
  toFun f := fun i => f (i + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Truncation to a window of length `n`, curried into the Hankel row
    index type. -/
def truncL (p : ℕ) (𝕜 : Type*) [Field 𝕜] (n : ℕ) :
    Germ p 𝕜 →ₗ[𝕜] (Fin n × Fin p → 𝕜) where
  toFun f := fun x => f x.1 x.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem shiftL_colGerm (g : Behavior p m 𝕜) (j : ℕ) (b : Fin m) :
    shiftL p 𝕜 (colGerm g j b) = colGerm g (j + 1) b := by
  funext i a
  show g ((i + 1) + j) a b = g (i + (j + 1)) a b
  rw [add_right_comm, add_assoc]

theorem shiftL_mem_stateSpace (g : Behavior p m 𝕜) {x : Germ p 𝕜}
    (hx : x ∈ stateSpace g) : shiftL p 𝕜 x ∈ stateSpace g := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨⟨j, b⟩, rfl⟩ := hy
      rw [shiftL_colGerm]
      exact Submodule.subset_span ⟨(j + 1, b), rfl⟩
  | zero => simpa using Submodule.zero_mem _
  | add y z _ _ hy hz => simpa [map_add] using Submodule.add_mem _ hy hz
  | smul c y _ hy => simpa [map_smul] using Submodule.smul_mem _ c hy

theorem stateSpaceUpTo_le (g : Behavior p m 𝕜) (N : ℕ) :
    stateSpaceUpTo g N ≤ stateSpace g := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨j, b⟩, rfl⟩
  exact Submodule.subset_span ⟨((j : ℕ), b), rfl⟩

theorem stateSpaceUpTo_mono (g : Behavior p m 𝕜) {N N' : ℕ} (h : N ≤ N') :
    stateSpaceUpTo g N ≤ stateSpaceUpTo g N' := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨j, b⟩, rfl⟩
  exact Submodule.subset_span ⟨(Fin.castLE h j, b), rfl⟩

/-- Staircase recursion: adding one more shift level. -/
theorem stateSpaceUpTo_succ (g : Behavior p m 𝕜) (N : ℕ) :
    stateSpaceUpTo g (N + 1)
      = stateSpaceUpTo g 1 ⊔ Submodule.map (shiftL p 𝕜) (stateSpaceUpTo g N) := by
  sorry

/-- The union of the truncated state spaces is the state space. -/
theorem iSup_stateSpaceUpTo (g : Behavior p m 𝕜) :
    (⨆ N, stateSpaceUpTo g N) = stateSpace g := by
  sorry

/-- The Hankel rank as the dimension of the truncated-image space. -/
theorem hankel_rank_eq_finrank_map (g : Behavior p m 𝕜) (n : ℕ) :
    (hankel g n).rank
      = finrank 𝕜 (Submodule.map (truncL p 𝕜 n) (stateSpaceUpTo g n)) := by
  sorry

/-- On a finite-dimensional subspace of germs, some finite truncation is
    already injective. -/
theorem exists_trunc_injective (W : Submodule 𝕜 (Germ p 𝕜))
    [FiniteDimensional 𝕜 W] :
    ∃ N : ℕ, ∀ w ∈ W, (∀ x : Fin N × Fin p, truncL p 𝕜 N w x = 0) → w = 0 := by
  sorry

/-- Master lemma (iii): uniformly bounded Hankel ranks force the state
    space to be finite-dimensional of dimension at most the bound. -/
theorem stateSpace_findim_of_rank_le (g : Behavior p m 𝕜) (d : ℕ)
    (hb : ∀ n, (hankel g n).rank ≤ d) :
    FiniteDimensional 𝕜 (stateSpace g) ∧ finrank 𝕜 (stateSpace g) ≤ d := by
  sorry

/-- Master lemma (iv): a finite-dimensional state space realizes `g` at
    dimension exactly its dimension. -/
theorem exists_realizes_of_findim (g : Behavior p m 𝕜)
    [FiniteDimensional 𝕜 (stateSpace g)] :
    ∃ R : Real p m (finrank 𝕜 (stateSpace g)) 𝕜, Realizes R g := by
  sorry

/-- Master lemma (v): once the window reaches the state-space dimension,
    every Hankel rank equals it. -/
theorem hankel_rank_stabilizes (g : Behavior p m 𝕜)
    [FiniteDimensional 𝕜 (stateSpace g)] {n : ℕ}
    (hn : finrank 𝕜 (stateSpace g) ≤ n) :
    (hankel g n).rank = finrank 𝕜 (stateSpace g) := by
  sorry

end Solution
end Realization
