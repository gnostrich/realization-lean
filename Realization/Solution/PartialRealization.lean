/-
Solution — the partial-realization core (finite Gragg–Lindquist /
Ho–Kalman–Tether existence): any window of `n` Markov parameters is
matched by a realization of dimension at most the rank of the size-`n`
square Hankel block. Load-bearing lemma for Block S invariants I1 ∧ I2.
-/
import Realization.Solution.Basic

open Matrix BigOperators

set_option linter.unusedSectionVars false

noncomputable section
namespace Realization
namespace Solution

variable {𝕜 : Type*} [Field 𝕜] {p m : ℕ}

/-- Partial realization at the covering square-Hankel rank. -/
theorem exists_partial_realization (g : Behavior p m 𝕜) (n : ℕ) :
    ∃ d' : ℕ, d' ≤ (hankel g n).rank ∧
      ∃ R : Real p m d' 𝕜, MatchesPrefix R g n := by
  sorry

end Solution
end Realization
