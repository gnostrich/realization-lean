/-
Solution — base layer (Stage 3, milestone: Hankel API + easy spine facts).
All statements here either restate frozen claims verbatim (namespace
`Realization.Solution`, same types against the same frozen definitions) or
are auxiliary lemmas. No frozen statement is modified.
-/
import Realization.Challenge

open Matrix BigOperators

set_option linter.unusedSectionVars false

noncomputable section
namespace Realization
namespace Solution

variable {𝕜 : Type*} [Field 𝕜]

/-! ### T2: unobservable content contributes nothing (frozen statement) -/

theorem unobservable_no_transfer {p m d : ℕ} (R : Real p m d 𝕜)
    (v : Fin d → 𝕜) (hv : ∀ k, R.C.mulVec ((R.A ^ k).mulVec v) = 0) :
    ∀ k, (R.C * (R.A ^ k)).mulVec v = 0 := by
  intro k
  rw [← Matrix.mulVec_mulVec]
  exact hv k

/-! ### Selection matrices -/

/-- The 0/1 selection matrix of a map `f : α → β`. -/
def selMat (𝕜 : Type*) [Field 𝕜] {α β : Type*} [DecidableEq β] (f : α → β) :
    Matrix α β 𝕜 :=
  Matrix.of fun a b => if b = f a then 1 else 0

theorem selMat_mul_transpose {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) :
    selMat 𝕜 f * (selMat 𝕜 f)ᵀ = 1 := by
  funext a a'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selMat, Matrix.of_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases haa : a = a'
  · subst haa; simp [Matrix.one_apply]
  · have hne : ¬ (f a = f a') := fun hc => haa (hf hc)
    simp [Matrix.one_apply, haa, hne]

theorem submatrix_eq_selMat_mul {α β α' β' : Type*} [Fintype α'] [Fintype β']
    [DecidableEq α'] [DecidableEq β'] (A : Matrix α' β' 𝕜)
    (f : α → α') (g : β → β') :
    A.submatrix f g = selMat 𝕜 f * A * (selMat 𝕜 g)ᵀ := by
  funext a b
  show A (f a) (g b) = ((selMat 𝕜 f * A) * (selMat 𝕜 g)ᵀ) a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selMat, Matrix.of_apply,
    ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Rank of an arbitrary submatrix is at most the rank. -/
theorem rank_submatrix_le' {α β α' β' : Type*} [Fintype α] [Fintype β]
    [Fintype α'] [Fintype β'] [DecidableEq α'] [DecidableEq β']
    (A : Matrix α' β' 𝕜) (f : α → α') (g : β → β') :
    (A.submatrix f g).rank ≤ A.rank := by
  rw [submatrix_eq_selMat_mul A f g]
  exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)

/-! ### Hankel API -/

/-- Hankel blocks are nested: smaller windows are submatrices. -/
theorem hankel_submatrix {p m : ℕ} (g : Behavior p m 𝕜) {n n' : ℕ}
    (h : n ≤ n') :
    hankel g n = (hankel g n').submatrix
      (fun x => (⟨Fin.castLE h x.1, x.2⟩ : Fin n' × Fin p))
      (fun y => (⟨Fin.castLE h y.1, y.2⟩ : Fin n' × Fin m)) := by
  ext x y
  rfl

/-- Hankel rank is monotone in the window size. -/
theorem hankel_rank_mono {p m : ℕ} (g : Behavior p m 𝕜) {n n' : ℕ}
    (h : n ≤ n') : (hankel g n).rank ≤ (hankel g n').rank := by
  rw [hankel_submatrix g h]
  exact rank_submatrix_le' _ _ _

/-- Observability-times-controllability factorization of a realized Hankel
    block: `hankel g n = O * Ctr` with inner index `Fin d`. -/
theorem hankel_eq_obs_mul_ctr {p m d : ℕ} {g : Behavior p m 𝕜}
    {R : Real p m d 𝕜} (h : Realizes R g) (n : ℕ) :
    hankel g n =
      (Matrix.of fun (x : Fin n × Fin p) (c : Fin d) =>
        (R.C * R.A ^ (x.1 : ℕ)) x.2 c) *
      (Matrix.of fun (c : Fin d) (y : Fin n × Fin m) =>
        (R.A ^ (y.1 : ℕ) * R.B) c y.2) := by
  funext x y
  have hg : g ((x.1 : ℕ) + (y.1 : ℕ))
      = R.C * R.A ^ ((x.1 : ℕ) + (y.1 : ℕ)) * R.B := by
    rw [← h]; rfl
  show g ((x.1 : ℕ) + (y.1 : ℕ)) x.2 y.2 = _
  have hsplit : R.C * R.A ^ ((x.1 : ℕ) + (y.1 : ℕ)) * R.B
      = (R.C * R.A ^ (x.1 : ℕ)) * (R.A ^ (y.1 : ℕ) * R.B) := by
    rw [pow_add]
    simp only [Matrix.mul_assoc]
  rw [hg, hsplit]
  simp [Matrix.mul_apply]

/-- A realization of dimension `d` bounds every finite Hankel rank by `d`. -/
theorem rank_hankel_le_of_realizes {p m d : ℕ} {g : Behavior p m 𝕜}
    {R : Real p m d 𝕜} (h : Realizes R g) (n : ℕ) :
    (hankel g n).rank ≤ d := by
  rw [hankel_eq_obs_mul_ctr h n]
  refine le_trans (Matrix.rank_mul_le_left _ _) ?_
  simpa using Matrix.rank_le_card_width
    (Matrix.of fun (x : Fin n × Fin p) (c : Fin d) =>
      (R.C * R.A ^ (x.1 : ℕ)) x.2 c)

/-- McMillan degree is a lower bound for any realizing dimension. -/
theorem mcMillan_le_of_realizes {p m d : ℕ} {g : Behavior p m 𝕜}
    {R : Real p m d 𝕜} (h : Realizes R g) : mcMillan g ≤ (d : ℕ∞) :=
  sInf_le ⟨d, rfl, R, h⟩

/-- If the McMillan degree is the finite value `d`, some dimension-`d`
    realization attains it. -/
theorem exists_realization_of_mcMillan_eq {p m d : ℕ} {g : Behavior p m 𝕜}
    (h : mcMillan g = (d : ℕ∞)) : ∃ R : Real p m d 𝕜, Realizes R g := by
  have hne : {e : ℕ∞ | ∃ d' : ℕ, e = d' ∧
      ∃ R : Real p m d' 𝕜, Realizes R g}.Nonempty := by
    rw [Set.nonempty_def]
    by_contra hempty
    push_neg at hempty
    have htop : mcMillan g = ⊤ := by
      rw [mcMillan, sInf_eq_top]
      intro b hb
      exact absurd hb (by simpa using hempty b)
    rw [h] at htop
    exact (WithTop.natCast_ne_top d) htop
  have hmem : mcMillan g ∈ {e : ℕ∞ | ∃ d' : ℕ, e = d' ∧
      ∃ R : Real p m d' 𝕜, Realizes R g} := csInf_mem hne
  rw [h] at hmem
  obtain ⟨d', hd', R, hR⟩ := hmem
  have hden : d = d' := by exact_mod_cast hd'
  subst hden
  exact ⟨R, hR⟩

/-- Consequently the McMillan degree bounds every finite Hankel rank. -/
theorem rank_hankel_le_mcMillan {p m d : ℕ} {g : Behavior p m 𝕜}
    (h : mcMillan g = (d : ℕ∞)) (n : ℕ) :
    (hankel g n).rank ≤ d := by
  obtain ⟨R, hR⟩ := exists_realization_of_mcMillan_eq h
  exact rank_hankel_le_of_realizes hR n

/-! ### Padding: a dimension-`r` realization embeds in any dimension
    `d ≥ r` with the same behavior. -/

/-- Pad a realization with zero blocks up to dimension `d`, along the
    inclusion `Fin.castLE`. -/
def padReal {p m r : ℕ} (R : Real p m r 𝕜) (d : ℕ) (h : r ≤ d) :
    Real p m d 𝕜 where
  A := (selMat 𝕜 (Fin.castLE h))ᵀ * R.A * selMat 𝕜 (Fin.castLE h)
  B := (selMat 𝕜 (Fin.castLE h))ᵀ * R.B
  C := R.C * selMat 𝕜 (Fin.castLE h)

theorem padReal_behavior {p m r : ℕ} (R : Real p m r 𝕜) (d : ℕ) (h : r ≤ d) :
    (padReal R d h).behavior = R.behavior := by
  have hPP : selMat 𝕜 (Fin.castLE h) * (selMat 𝕜 (Fin.castLE h))ᵀ = 1 :=
    selMat_mul_transpose (Fin.castLE_injective h)
  set Q : Matrix (Fin r) (Fin d) 𝕜 := selMat 𝕜 (Fin.castLE h) with hQ
  have key : ∀ k : ℕ, Q * (Qᵀ * R.A * Q) ^ k * Qᵀ = R.A ^ k := by
    intro k
    induction k with
    | zero => simpa using hPP
    | succ k ih =>
        rw [pow_succ, pow_succ]
        calc Q * ((Qᵀ * R.A * Q) ^ k * (Qᵀ * R.A * Q)) * Qᵀ
            = (Q * (Qᵀ * R.A * Q) ^ k * Qᵀ) * R.A * (Q * Qᵀ) := by
              simp only [Matrix.mul_assoc]
          _ = R.A ^ k * R.A * 1 := by rw [ih, hPP]
          _ = R.A ^ k * R.A := by rw [Matrix.mul_one]
  funext k
  show R.C * Q * (Qᵀ * R.A * Q) ^ k * (Qᵀ * R.B) = R.C * R.A ^ k * R.B
  calc R.C * Q * (Qᵀ * R.A * Q) ^ k * (Qᵀ * R.B)
      = R.C * (Q * (Qᵀ * R.A * Q) ^ k * Qᵀ) * R.B := by
        simp only [Matrix.mul_assoc]
    _ = R.C * R.A ^ k * R.B := by rw [key k]

theorem padReal_realizes {p m r : ℕ} {R : Real p m r 𝕜} {g : Behavior p m 𝕜}
    (hR : Realizes R g) (d : ℕ) (h : r ≤ d) : Realizes (padReal R d h) g := by
  unfold Realizes at hR ⊢
  rw [padReal_behavior, hR]

theorem padReal_matchesPrefix {p m r : ℕ} {R : Real p m r ℚ}
    {g : Behavior p m ℚ} {n : ℕ} (hR : MatchesPrefix R g n) (d : ℕ)
    (h : r ≤ d) : MatchesPrefix (padReal R d h) g n := by
  intro k hk
  rw [show (padReal R d h).behavior = R.behavior from padReal_behavior R d h]
  exact hR k hk

/-- Realizability at dimension `r` and `r ≤ d` give realizability at `d`. -/
theorem exists_realization_mono {p m r d : ℕ} {g : Behavior p m 𝕜}
    (h : ∃ R : Real p m r 𝕜, Realizes R g) (hrd : r ≤ d) :
    ∃ R : Real p m d 𝕜, Realizes R g := by
  obtain ⟨R, hR⟩ := h
  exact ⟨padReal R d hrd, padReal_realizes hR d hrd⟩

/-! ### The zero behavior and dimension zero -/

/-- The unique dimension-0 realization realizes exactly the zero behavior. -/
theorem realizes_zero_of_dim_zero {p m : ℕ} (R : Real p m 0 𝕜) :
    Realizes R (fun _ => (0 : Matrix (Fin p) (Fin m) 𝕜)) := by
  funext k
  show R.C * R.A ^ k * R.B = 0
  apply Matrix.ext
  intro a b
  simp [Matrix.mul_apply]

theorem mcMillan_zero {p m : ℕ} :
    mcMillan (fun _ => (0 : Matrix (Fin p) (Fin m) 𝕜)) = 0 := by
  have h0 : (0 : ℕ∞) ∈ {e : ℕ∞ | ∃ d' : ℕ, e = d' ∧
      ∃ R : Real p m d' 𝕜, Realizes R (fun _ => 0)} := by
    refine ⟨0, by norm_num, ⟨⟨0, 0, 0⟩, realizes_zero_of_dim_zero _⟩⟩
  exact le_antisymm (sInf_le h0) (zero_le _)

end Solution
end Realization
