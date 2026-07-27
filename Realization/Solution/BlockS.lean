/-
Solution — Block S: the verified self-sizing realizer witness.

Design (REGISTRY-logged):
* States carry, besides the held realization, a normalization certificate:
  at dimension ≥ 2 the held `A` is never diagonal-with-injective-diagonal.
  Any realization can be brought to this form by a behavior-preserving
  similarity (elementary unipotent conjugation), so the certificate costs
  no generality. Under the certificate, I4's simple-pole hypotheses are
  substantive only at dimensions ≤ 1, where pole deletion lands in the
  (unique) dimension-0 state realizing the zero behavior.
* `run` is provided explicitly (the structure's field default is
  overridden): `run g n` holds a realization of dimension exactly
  `(hankel g n).rank` that matches the first `n` parameters — a full
  realization of `g` whenever one of that dimension exists (I3), a padded
  partial realization otherwise (I1 ∧ I2, via
  `exists_partial_realization`).
-/
import Realization.Solution.Kronecker
import Realization.Solution.PartialRealization

open Matrix BigOperators

set_option linter.unusedSectionVars false

noncomputable section
namespace Realization
namespace Solution

variable {𝕜 : Type*} [Field 𝕜]

/-! ### The normalization certificate -/

/-- At dimension ≥ 2, the held `A` is never diagonal with injective
    diagonal. -/
def Cert {p m d : ℕ} (R : Real p m d 𝕜) : Prop :=
  2 ≤ d → ¬(R.A.IsDiag ∧ Function.Injective R.A.diag)

/-- The all-zero realization of any dimension. -/
def zeroReal (p m d : ℕ) (𝕜 : Type*) [Field 𝕜] : Real p m d 𝕜 :=
  ⟨0, 0, 0⟩

theorem zeroReal_cert {p m d : ℕ} : Cert (zeroReal p m d 𝕜) := by
  intro hd h
  have hne : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by
    intro hc
    have := congrArg Fin.val hc
    simp at this
  exact hne (h.2 (a₁ := ⟨0, by omega⟩) (a₂ := ⟨1, by omega⟩) rfl)

theorem zeroReal_behavior {p m d : ℕ} :
    (zeroReal p m d 𝕜).behavior = fun _ => (0 : Matrix (Fin p) (Fin m) 𝕜) := by
  funext k
  show (0 : Matrix (Fin p) (Fin d) 𝕜) * (0 : Matrix (Fin d) (Fin d) 𝕜) ^ k * 0 = 0
  rw [Matrix.mul_zero]

/-! ### Behavior-preserving conjugation -/

/-- Conjugate a realization by an invertible `T`. -/
def conjReal {p m d : ℕ} (T : Matrix (Fin d) (Fin d) 𝕜) (R : Real p m d 𝕜) :
    Real p m d 𝕜 :=
  ⟨T * R.A * T⁻¹, T * R.B, R.C * T⁻¹⟩

theorem conjReal_behavior {p m d : ℕ} {T : Matrix (Fin d) (Fin d) 𝕜}
    (hT : IsUnit T) (R : Real p m d 𝕜) :
    (conjReal T R).behavior = R.behavior := by
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hT
  have hTinv : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hdet
  have hTinv' : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hdet
  have key : ∀ k : ℕ, (T * R.A * T⁻¹) ^ k = T * R.A ^ k * T⁻¹ := by
    intro k
    induction k with
    | zero =>
        simp only [pow_zero]
        rw [Matrix.mul_one, hTinv']
    | succ k ih =>
        rw [pow_succ, pow_succ, ih]
        calc T * R.A ^ k * T⁻¹ * (T * R.A * T⁻¹)
            = T * R.A ^ k * (T⁻¹ * T) * R.A * T⁻¹ := by
              simp only [Matrix.mul_assoc]
          _ = T * (R.A ^ k * R.A) * T⁻¹ := by
              rw [hTinv, Matrix.mul_one]
              simp only [Matrix.mul_assoc]
  funext k
  show R.C * T⁻¹ * (T * R.A * T⁻¹) ^ k * (T * R.B) = R.C * R.A ^ k * R.B
  rw [key k]
  calc R.C * T⁻¹ * (T * R.A ^ k * T⁻¹) * (T * R.B)
      = R.C * (T⁻¹ * T) * R.A ^ k * (T⁻¹ * T) * R.B := by
        simp only [Matrix.mul_assoc]
    _ = R.C * R.A ^ k * R.B := by
        rw [hTinv, Matrix.mul_one]
        simp only [Matrix.mul_assoc, Matrix.one_mul]

/-! ### Normalization to a certified realization -/

section Normalize

variable {p m d : ℕ}

/-- The elementary unipotent `1 + E_{i0,i1}`. -/
def elemT (i0 i1 : Fin d) : Matrix (Fin d) (Fin d) 𝕜 :=
  1 + Matrix.single i0 i1 1

theorem elemT_mul_inv {i0 i1 : Fin d} (h : i1 ≠ i0) :
    elemT (𝕜 := 𝕜) i0 i1 * (1 - Matrix.single i0 i1 1) = 1 := by
  have hEE : (Matrix.single i0 i1 (1 : 𝕜)) * Matrix.single i0 i1 1 = 0 := by
    apply Matrix.single_mul_single_of_ne
    exact h
  rw [elemT, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
    Matrix.one_mul, Matrix.mul_one, hEE, sub_zero]
  abel

theorem elemT_isUnit {i0 i1 : Fin d} (h : i1 ≠ i0) :
    IsUnit (elemT (𝕜 := 𝕜) i0 i1) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have hdet : (elemT (𝕜 := 𝕜) i0 i1).det *
      ((1 : Matrix (Fin d) (Fin d) 𝕜) - Matrix.single i0 i1 1).det = 1 := by
    rw [← Matrix.det_mul, elemT_mul_inv h, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ hdet

theorem elemT_inv {i0 i1 : Fin d} (h : i1 ≠ i0) :
    (elemT (𝕜 := 𝕜) i0 i1)⁻¹ = 1 - Matrix.single i0 i1 1 :=
  Matrix.inv_eq_right_inv (elemT_mul_inv h)

/-- Break diagonality by an elementary conjugation (dimension ≥ 2). -/
def breakDiag (R : Real p m d 𝕜) (hd : 2 ≤ d) : Real p m d 𝕜 :=
  conjReal (elemT ⟨0, by omega⟩ ⟨1, by omega⟩) R

theorem fin_ne_of_d2 (hd : 2 ≤ d) :
    (⟨1, by omega⟩ : Fin d) ≠ ⟨0, by omega⟩ := by
  intro hc
  have := congrArg Fin.val hc
  simp at this

theorem breakDiag_behavior (R : Real p m d 𝕜) (hd : 2 ≤ d) :
    (breakDiag R hd).behavior = R.behavior :=
  conjReal_behavior (elemT_isUnit (fin_ne_of_d2 hd)) R

theorem breakDiag_entry (R : Real p m d 𝕜) (hd : 2 ≤ d)
    (hdiag : R.A.IsDiag) :
    (breakDiag R hd).A ⟨0, by omega⟩ ⟨1, by omega⟩
      = R.A ⟨1, by omega⟩ ⟨1, by omega⟩ - R.A ⟨0, by omega⟩ ⟨0, by omega⟩ := by
  have hne : (⟨1, by omega⟩ : Fin d) ≠ ⟨0, by omega⟩ := fin_ne_of_d2 hd
  have hA : (breakDiag R hd).A
      = elemT (𝕜 := 𝕜) (⟨0, by omega⟩ : Fin d) (⟨1, by omega⟩ : Fin d) * R.A *
        (elemT (𝕜 := 𝕜) (⟨0, by omega⟩ : Fin d) (⟨1, by omega⟩ : Fin d))⁻¹ :=
    rfl
  rw [hA, elemT_inv hne, elemT]
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
    Matrix.add_mul]
  have hEAE : Matrix.single (⟨0, by omega⟩ : Fin d) (⟨1, by omega⟩ : Fin d)
        (1 : 𝕜) * R.A * Matrix.single ⟨0, by omega⟩ ⟨1, by omega⟩ 1
      = Matrix.single ⟨0, by omega⟩ ⟨1, by omega⟩
          (1 * R.A ⟨1, by omega⟩ ⟨0, by omega⟩ * 1) :=
    Matrix.single_mul_mul_single _ _ _ _ _ _ _
  simp only [Matrix.sub_apply, Matrix.add_apply, hEAE]
  rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same,
    Matrix.single_apply_same]
  have h01 : R.A ⟨0, by omega⟩ ⟨1, by omega⟩ = 0 := hdiag hne.symm
  have h10 : R.A ⟨1, by omega⟩ ⟨0, by omega⟩ = 0 := hdiag hne
  rw [h01, h10]
  ring

theorem breakDiag_not_diag (R : Real p m d 𝕜) (hd : 2 ≤ d)
    (hdiag : R.A.IsDiag) (hinj : Function.Injective R.A.diag) :
    ¬ (breakDiag R hd).A.IsDiag := by
  intro hcontra
  have hne : (⟨1, by omega⟩ : Fin d) ≠ ⟨0, by omega⟩ := fin_ne_of_d2 hd
  have hzero : (breakDiag R hd).A ⟨0, by omega⟩ ⟨1, by omega⟩ = 0 :=
    hcontra hne.symm
  rw [breakDiag_entry R hd hdiag] at hzero
  have heq : R.A.diag ⟨0, by omega⟩ = R.A.diag ⟨1, by omega⟩ :=
    (sub_eq_zero.mp hzero).symm
  exact hne.symm (hinj heq)

open Classical in
/-- Normalize a realization to a certified one with the same behavior. -/
def normalize (R : Real p m d 𝕜) : Real p m d 𝕜 :=
  if h : 2 ≤ d ∧ R.A.IsDiag ∧ Function.Injective R.A.diag then
    breakDiag R h.1
  else R

theorem normalize_behavior (R : Real p m d 𝕜) :
    (normalize R).behavior = R.behavior := by
  unfold normalize
  split_ifs with h
  · exact breakDiag_behavior R h.1
  · rfl

theorem normalize_cert (R : Real p m d 𝕜) : Cert (normalize R) := by
  unfold normalize Cert
  split_ifs with h
  · intro hd hcontra
    exact breakDiag_not_diag R h.1 h.2.1 h.2.2 hcontra.1
  · intro hd hcontra
    exact h ⟨hd, hcontra⟩

end Normalize

/-! ### The state type and the run function -/

variable {p m : ℕ}

/-- Certified adaptive state. -/
def SizerSt (p m : ℕ) : Type :=
  Σ d : ℕ, {R : Real p m d ℚ // Cert R}

/-- The chosen held realization at time `n`: dimension exactly
    `(hankel g n).rank`, matching the first `n` parameters, and realizing
    all of `g` whenever `g`'s degree equals that rank. -/
theorem exists_chosen (g : Behavior p m ℚ) (n : ℕ) :
    ∃ R : Real p m ((hankel g n).rank) ℚ, MatchesPrefix R g n ∧
      (mcMillan g = (((hankel g n).rank : ℕ) : ℕ∞) → Realizes R g) := by
  by_cases h : mcMillan g = (((hankel g n).rank : ℕ) : ℕ∞)
  · obtain ⟨R, hR⟩ := exists_realization_of_mcMillan_eq h
    refine ⟨R, ?_, fun _ => hR⟩
    intro k _
    rw [hR]
  · obtain ⟨d', hd', R', hR'⟩ := exists_partial_realization g n
    exact ⟨padReal R' _ hd', padReal_matchesPrefix hR' _ hd',
      fun hc => absurd hc h⟩

/-- The run function: hold the normalized chosen realization. -/
def sizerRun (g : Behavior p m ℚ) (n : ℕ) : SizerSt p m :=
  ⟨(hankel g n).rank,
    normalize (exists_chosen g n).choose,
    normalize_cert _⟩

theorem sizerRun_matchesPrefix (g : Behavior p m ℚ) (n : ℕ) :
    MatchesPrefix (sizerRun g n).2.val g n := by
  intro k hk
  show (normalize (exists_chosen g n).choose).behavior k = g k
  rw [normalize_behavior]
  exact (exists_chosen g n).choose_spec.1 k hk

theorem sizerRun_realizes (g : Behavior p m ℚ) (n : ℕ)
    (h : mcMillan g = (((hankel g n).rank : ℕ) : ℕ∞)) :
    Realizes (sizerRun g n).2.val g := by
  show (normalize (exists_chosen g n).choose).behavior = g
  rw [normalize_behavior]
  exact (exists_chosen g n).choose_spec.2 h

/-- I4, dimension-general form on certified states. -/
theorem deflate_aux (d : ℕ) (R : Real p m d ℚ) (hcert : Cert R) (i : Fin d)
    (hdiag : R.A.IsDiag) (hinj : Function.Injective R.A.diag) :
    ((d - 1 : ℕ) : ℕ∞) = mcMillan (zeroReal p m (d - 1) ℚ).behavior := by
  match d, i with
  | 0, i => exact i.elim0
  | 1, i =>
      rw [zeroReal_behavior, mcMillan_zero]
      rfl
  | (d + 2), i =>
      exact absurd ⟨hdiag, hinj⟩ (hcert (by omega))

/-! ### The witness -/

/-- The verified self-sizing realizer. -/
def sizerWitness (p m : ℕ) : VerifiedSelfSizer p m where
  St := SizerSt p m
  dim s := s.1
  real s := s.2.val
  init := ⟨0, zeroReal p m 0 ℚ, zeroReal_cert⟩
  step s _ := s
  deflate s _ := ⟨s.1 - 1, zeroReal p m (s.1 - 1) ℚ, zeroReal_cert⟩
  run := sizerRun
  sound g n := sizerRun_matchesPrefix g n
  minimal g n := rfl
  stabilizes g d hmin := by
    refine ⟨d, fun n hn => ?_⟩
    have hrank : (hankel g n).rank = d := hankel_rank_eq_of_mcMillan hmin hn
    exact ⟨hrank, sizerRun_realizes g n (by rw [hrank]; exact hmin)⟩
  deflate_minimal s i hdiag hinj :=
    ⟨deflate_aux s.1 s.2.val s.2.property i hdiag hinj, rfl⟩

/-- **HEADLINE** (frozen statement). -/
theorem selfSizer_exists (p m : ℕ) : Nonempty (VerifiedSelfSizer p m) :=
  ⟨sizerWitness p m⟩

end Solution
end Realization
