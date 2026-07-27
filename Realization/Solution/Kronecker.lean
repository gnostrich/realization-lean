/-
Solution — assembly layer over the state-space framework: Kronecker
realizability (frozen statement), McMillan degree = state-space dimension,
and Hankel-rank stabilization at the degree.
-/
import Realization.Solution.StateSpace

open Matrix BigOperators Module

set_option linter.unusedSectionVars false

noncomputable section
namespace Realization
namespace Solution

variable {𝕜 : Type*} [Field 𝕜] {p m : ℕ}

/-- **Kronecker realizability** (frozen statement): realizable in
    dimension `d` iff every finite Hankel rank is at most `d`. -/
theorem kronecker_realizability {p m d : ℕ} (g : Behavior p m 𝕜) :
    (∃ R : Real p m d 𝕜, Realizes R g) ↔ (∀ n, (hankel g n).rank ≤ d) := by
  constructor
  · rintro ⟨R, hR⟩ n
    exact rank_hankel_le_of_realizes hR n
  · intro hb
    obtain ⟨hfd, hle⟩ := stateSpace_findim_of_rank_le g d hb
    haveI := hfd
    exact exists_realization_mono (exists_realizes_of_findim g) hle

/-- The McMillan degree of a finite-degree behavior is the dimension of
    its state space. -/
theorem stateSpace_finrank_of_mcMillan {g : Behavior p m 𝕜} {d : ℕ}
    (hmin : mcMillan g = (d : ℕ∞)) :
    FiniteDimensional 𝕜 (stateSpace g) ∧ finrank 𝕜 (stateSpace g) = d := by
  obtain ⟨hfd, hle⟩ :=
    stateSpace_findim_of_rank_le g d (rank_hankel_le_mcMillan hmin)
  haveI := hfd
  refine ⟨hfd, le_antisymm hle ?_⟩
  have h1 : mcMillan g ≤ (finrank 𝕜 (stateSpace g) : ℕ∞) :=
    mcMillan_le_of_realizes (exists_realizes_of_findim g).choose_spec
  rw [hmin] at h1
  exact_mod_cast h1

/-- **Rank stabilization at the degree** (the true growth rule): a
    behavior of McMillan degree `d` has Hankel rank exactly `d` at every
    window size `n ≥ d`. -/
theorem hankel_rank_eq_of_mcMillan {g : Behavior p m 𝕜} {d n : ℕ}
    (hmin : mcMillan g = (d : ℕ∞)) (hn : d ≤ n) :
    (hankel g n).rank = d := by
  obtain ⟨hfd, hfr⟩ := stateSpace_finrank_of_mcMillan hmin
  haveI := hfd
  rw [← hfr] at hn ⊢
  exact hankel_rank_stabilizes g hn

end Solution
end Realization
