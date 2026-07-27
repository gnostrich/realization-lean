/-
Solution — logged statement defects, machine-checked (negatives are
first-class). The refutations below are proved against the SAME frozen
definitions the challenge uses; the defective frozen statements stay
`sorry` in Challenge.lean per protocol.
-/
import Realization.Challenge

open Matrix BigOperators Module

set_option linter.unusedSectionVars false

noncomputable section
namespace Realization
namespace Solution

/-- The frozen `growth_test_correct` statement is FALSE: its hypotheses
only constrain `g 0 .. g (2r+2)`, while its conclusion constrains every
window. Witness: `r = 0`, `g k = 0` for `k ≤ 2` and `g 3 = 1`. -/
theorem growth_test_correct_is_false :
    ¬ (∀ (g : Behavior 1 1 ℚ) (r : ℕ),
        (hankel g (r + 1)).rank = r → (hankel g (r + 2)).rank = r →
        (∀ n, r ≤ n → (hankel g n).rank = r) ∧ mcMillan g = (r : ℕ∞)) := by
  intro h
  let g : Behavior 1 1 ℚ := fun k _ _ => if k ≤ 2 then 0 else 1
  have h1mat : hankel g 1 = 0 := by
    ext x y
    simp [hankel, g]
  have h2mat : hankel g 2 = 0 := by
    ext x y
    simp [hankel, g]
    omega
  have hg := h g 0 (by rw [h1mat]; exact Matrix.rank_zero)
    (by rw [h2mat]; exact Matrix.rank_zero)
  have h3 : (hankel g 3).rank = 0 := hg.1 3 (Nat.zero_le 3)
  let i : Fin 3 × Fin 1 := (⟨1, by omega⟩, 0)
  let j : Fin 3 × Fin 1 := (⟨2, by omega⟩, 0)
  let v : (Fin 3 × Fin 1) → ℚ := Pi.single j 1
  have hzero : ∀ x : LinearMap.range (hankel g 3).mulVecLin, x = 0 := by
    apply (finrank_zero_iff_forall_zero (K := ℚ)).mp
    exact h3
  have hzsub := hzero ⟨(hankel g 3).mulVecLin v, ⟨v, rfl⟩⟩
  have hz : (hankel g 3).mulVecLin v = 0 := congrArg Subtype.val hzsub
  have hzentry := congrFun hz i
  simp [v, i, j, hankel, g, Matrix.mulVec_single] at hzentry

end Solution
end Realization
