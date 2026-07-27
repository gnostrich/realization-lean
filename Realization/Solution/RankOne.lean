/-
Solution — rank-one matrix factorization (support lemma for
graduation_frees_rank). Aristotle (project 3fb4ee5a); audit passed.
-/
import Realization.Solution.Basic

open Matrix BigOperators Module

set_option linter.unusedSectionVars false

noncomputable section
namespace Realization
namespace Solution

variable {𝕜 : Type*} [Field 𝕜]

lemma rank_one_matrix_factorization {p m : ℕ}
    (M : Matrix (Fin p) (Fin m) 𝕜) (hM : M ≠ 0) (hr : M.rank = 1) :
    ∃ c : Fin p → 𝕜, ∃ r : Fin m → 𝕜,
      c ≠ 0 ∧ r ≠ 0 ∧ M = Matrix.vecMulVec c r := by
  have hrpos : 0 < M.rank := hr.symm ▸ Nat.zero_lt_one
  have hdim : finrank 𝕜 (LinearMap.range M.mulVecLin) = 1 := by
    exact hr
  -- The range has a basis with one element
  have ⟨b, hb⟩ := finrank_eq_one_iff'.mp hdim
  -- b is a non-zero element in the range, so b = M.mulVec v for some v
  have hbne : b ≠ 0 := hb.1
  have hbspan : ∀ w : LinearMap.range M.mulVecLin, ∃ c : 𝕜, c • b = w := hb.2
  -- Extract the underlying vector
  have hv_range : (b : Fin p → 𝕜) ∈ LinearMap.range M.mulVecLin := b.2
  rw [LinearMap.mem_range] at hv_range
  obtain ⟨v, hv_eq⟩ := hv_range
  -- There exists some column j where M.mulVec e_j ≠ 0 (since M ≠ 0)
  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin m, M.mulVec (Pi.single j 1) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hM
    apply Matrix.ext
    intro i j
    have := congrFun (hall j) i
    simp at this
    simp [this]
  -- Use M.mulVec v as c (the spanning vector of the range)
  have hc_eq : M.mulVec v = b := by rw [← hv_eq]; rfl
  set c := M.mulVec v with hc_def
  -- For each column j, there exists r j such that column j = r j • c
  have hcol : ∀ j : Fin m, ∃ rj : 𝕜, M.mulVec (Pi.single j 1) = rj • c := by
    intro j
    have hw : (M.mulVec (Pi.single j 1)) ∈ LinearMap.range M.mulVecLin := ⟨_, rfl⟩
    obtain ⟨rj, hrj⟩ := hbspan ⟨M.mulVec (Pi.single j 1), hw⟩
    use rj
    have hvec : rj • (b : Fin p → 𝕜) = M.mulVec (Pi.single j 1) := by
      have := congr_arg Subtype.val hrj.symm
      simpa using this.symm
    rw [← hc_eq] at hvec
    exact hvec.symm
  choose r hr using hcol
  -- c ≠ 0
  have hc_ne : c ≠ 0 := by
    intro hc0
    apply hbne
    exact Subtype.ext (hc_eq.symm ▸ hc0)
  -- r ≠ 0 (since column j₀ is non-zero)
  have hr_ne : r ≠ 0 := by
    intro hr0
    apply hj₀
    rw [hr j₀]
    simp [hr0]
  -- M = vecMulVec c r
  have hM_eq : M = Matrix.vecMulVec c r := by
    ext i j
    have := congrFun (hr j) i
    simp [Matrix.vecMulVec] at this ⊢
    rw [mul_comm]
    exact this
  exact ⟨c, r, hc_ne, hr_ne, hM_eq⟩

end Solution
end Realization
