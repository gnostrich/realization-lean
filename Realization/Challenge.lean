/-
CHALLENGE FILE — realization-lean
Protocol: statements ARE the claims. Prose is not. Mathlib-only imports.
All `sorry`. Solution must prove EXACTLY these statements; comparator
verifies statement-match, per-theorem axiom allowlist, kernel acceptance.
Scope: finite-dimensional, EXACT arithmetic. Naming obeys CONFLATIONS.md
freeze table. Executing session repairs syntax/name-drift freely; any
SEMANTIC change is a STATEMENT-DEFECT: logged to REGISTRY, surfaced, never
silently patched.
-/
import Mathlib

open Matrix BigOperators

noncomputable section
namespace Realization

variable {𝕜 : Type*} [Field 𝕜]

/-- Interface behavior: the (p,m) Markov-parameter sequence. -/
def Behavior (p m : ℕ) (𝕜 : Type*) := ℕ → Matrix (Fin p) (Fin m) 𝕜

/-- State-space realization of dimension d. -/
structure Real (p m d : ℕ) (𝕜 : Type*) [Field 𝕜] where
  A : Matrix (Fin d) (Fin d) 𝕜
  B : Matrix (Fin d) (Fin m) 𝕜
  C : Matrix (Fin p) (Fin d) 𝕜

def Real.behavior {p m d : ℕ} (R : Real p m d 𝕜) : Behavior p m 𝕜 :=
  fun k => R.C * (R.A ^ k) * R.B

def Realizes {p m d : ℕ} (R : Real p m d 𝕜) (g : Behavior p m 𝕜) : Prop :=
  R.behavior = g

/-- Finite block-Hankel: blocks (i,j) ↦ g(i+j). -/
def hankel {p m : ℕ} (g : Behavior p m 𝕜) (n : ℕ) :
    Matrix (Fin n × Fin p) (Fin n × Fin m) 𝕜 :=
  fun x y => g (x.1.val + y.1.val) x.2 y.2

/-- McMillan degree: least realizable dimension (⊤ if none). -/
def mcMillan {p m : ℕ} (g : Behavior p m 𝕜) : ℕ∞ :=
  sInf {d : ℕ∞ | ∃ d' : ℕ, d = d' ∧ ∃ R : Real p m d' 𝕜, Realizes R g}

-- ══════════════ BLOCK C2 — THE SPINE (lemma layer of the headline object) ══════════════

theorem kronecker_realizability {p m d : ℕ} (g : Behavior p m 𝕜) :
    (∃ R : Real p m d 𝕜, Realizes R g) ↔ (∀ n, (hankel g n).rank ≤ d) := by
  sorry

theorem growth_test_correct {p m r : ℕ} (g : Behavior p m 𝕜)
    (h₁ : (hankel g (r + 1)).rank = r) (h₂ : (hankel g (r + 2)).rank = r) :
    (∀ n, r ≤ n → (hankel g n).rank = r) ∧ mcMillan g = (r : ℕ∞) := by
  sorry

theorem kalman_uniqueness {p m d : ℕ} (g : Behavior p m 𝕜)
    (R₁ R₂ : Real p m d 𝕜) (h₁ : Realizes R₁ g) (h₂ : Realizes R₂ g)
    (hmin : mcMillan g = (d : ℕ∞)) :
    ∃ S : Matrix (Fin d) (Fin d) 𝕜, IsUnit S ∧
      R₂.A = S * R₁.A * S⁻¹ ∧ R₂.B = S * R₁.B ∧ R₂.C = R₁.C * S⁻¹ := by
  sorry

theorem unobservable_no_transfer {p m d : ℕ} (R : Real p m d 𝕜)
    (v : Fin d → 𝕜) (hv : ∀ k, R.C.mulVec ((R.A ^ k).mulVec v) = 0) :
    ∀ k, (R.C * (R.A ^ k)).mulVec v = 0 := by
  sorry
-- Session: strengthen to observable-quotient form; strengthening is a
-- logged REGISTRY event.

theorem graduation_frees_rank {p m d : ℕ} (hd : 0 < d)
    (lam : Fin d → 𝕜) (hlam : Function.Injective lam)
    (Bv : Fin d → Matrix (Fin p) (Fin m) 𝕜) (hBv : ∀ i, Bv i ≠ 0)
    (hrank1 : ∀ i, (Bv i).rank = 1) (i₀ : Fin d) :
    mcMillan (fun k => ∑ i ∈ Finset.univ.erase i₀, (lam i) ^ k • Bv i)
      = ((d - 1 : ℕ) : ℕ∞) := by
  sorry

-- ══════════════ BLOCK C3 — REGRESSION LOCKS ══════════════

theorem schur_flag_gaming {n : ℕ} (T : Matrix (Fin n) (Fin n) 𝕜)
    (hT : T.BlockTriangular id) (k : ℕ) :
    (T ^ k).diag = (T.diag) ^ k := by
  sorry

theorem no_cost_floor :
    ∃ T : Matrix (Fin 2) (Fin 2) ℂ, T * Tᴴ ≠ Tᴴ * T ∧
      mcMillan (fun k => (Matrix.of ![![(T ^ k).diag 0]]) : Behavior 1 1 ℂ)
        ≤ (1 : ℕ∞) := by
  sorry

-- ══════════════ BLOCK C1 / C1' — SECTORS, STATICS, METER ══════════════

theorem skew_quadratic_null {n : ℕ} [NeZero (2 : 𝕜)]
    (S : Matrix (Fin n) (Fin n) 𝕜) (hS : Sᵀ = -S) (x : Fin n → 𝕜) :
    x ⬝ᵥ S.mulVec x = 0 := by
  sorry

theorem skew_symmetric_trace_zero {n : ℕ} [NeZero (2 : 𝕜)]
    (S H : Matrix (Fin n) (Fin n) 𝕜) (hS : Sᵀ = -S) (hH : Hᵀ = H) :
    (S * H).trace = 0 := by
  sorry

theorem transfer_defect_first_order {A₁ A₂ : Type*} [Ring A₁] [Ring A₂]
    (Φ₀ ψ : A₁ →+ A₂) (hΦ₀ : ∀ a b, Φ₀ (a * b) = Φ₀ a * Φ₀ b) (a b : A₁) :
    (Φ₀ + ψ) (a * b) - (Φ₀ + ψ) a * (Φ₀ + ψ) b
      = (ψ (a * b) - ψ a * Φ₀ b - Φ₀ a * ψ b) - ψ a * ψ b := by
  sorry

theorem tilt_displaces_uniquely {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : K.PosDef) (b t : Fin n → ℝ) :
    (∃! s, K.mulVec s = b) ∧
    (∀ s₀ s₁, K.mulVec s₀ = b → K.mulVec s₁ = b + t →
      s₁ = s₀ + K⁻¹.mulVec t) := by
  sorry

theorem sym_skew_unique_decomposition {n : ℕ} [NeZero (2 : 𝕜)]
    (A : Matrix (Fin n) (Fin n) 𝕜) :
    (∃! P : Matrix (Fin n) (Fin n) 𝕜 × Matrix (Fin n) (Fin n) 𝕜,
      P.1ᵀ = P.1 ∧ P.2ᵀ = -P.2 ∧ A = P.1 + P.2) ∧
    (∀ S : Matrix (Fin n) (Fin n) 𝕜, Sᵀ = S → Sᵀ = -S → S = 0) := by
  sorry

theorem symmetric_loop_work_zero {n m : ℕ} [NeZero (2 : 𝕜)]
    (H : Matrix (Fin n) (Fin n) 𝕜) (hH : Hᵀ = H)
    (x : Fin (m + 1) → Fin n → 𝕜) (hclosed : x (Fin.last m) = x 0) :
    ∑ i : Fin m, (2⁻¹ : 𝕜) •
      ((x i.castSucc + x i.succ) ⬝ᵥ H.mulVec (x i.succ - x i.castSucc)) = 0 := by
  sorry

-- ══════════════ BLOCK S — THE HEADLINE OBJECT: VERIFIED SELF-SIZING REALIZATION ══════════════
/-
The certificate AS an object: an executable fold over a behavior stream
holding a dimension-adaptive realization, with correctness as invariants.
Over ℚ the operations are computable: the proved object IS the deployed
object (F1 realignment by construction).
-/

/-- Prefix agreement: R matches the first n Markov parameters of g. -/
def MatchesPrefix {p m d : ℕ} (R : Real p m d 𝕜) (g : Behavior p m 𝕜)
    (n : ℕ) : Prop := ∀ k < n, R.behavior k = g k

/-- A verified self-sizing realizer over ℚ (computable field). -/
structure VerifiedSelfSizer (p m : ℕ) where
  /-- Adaptive state: current dimension + realization + certificate data. -/
  St : Type
  dim : St → ℕ
  real : (s : St) → Real p m (dim s) ℚ
  init : St
  /-- One step: consume the next Markov parameter. -/
  step : St → Matrix (Fin p) (Fin m) ℚ → St
  /-- Deflate: delete a designated pole (graduation). -/
  deflate : (s : St) → Fin (dim s) → St
  /-- run g n = state after consuming g 0, …, g (n−1). -/
  run : Behavior p m ℚ → ℕ → St :=
    fun g n => Nat.rec init (fun k s => step s (g k)) n
  /-- I1 SOUNDNESS: at every step, held realization matches all data seen. -/
  sound : ∀ (g : Behavior p m ℚ) (n : ℕ),
    MatchesPrefix (real (run g n)) g n
  /-- I2 MINIMALITY: held dimension = Hankel rank of the data seen —
      never over-sized, at every step. -/
  minimal : ∀ (g : Behavior p m ℚ) (n : ℕ),
    (dim (run g n) : ℕ∞) = ((hankel g n).rank : ℕ∞)
  /-- I3 STABILIZATION (coverage theorem): a degree-d source is reached in
      finitely many steps and the dimension NEVER changes again; from the
      stabilization point the held realization realizes ALL of g. -/
  stabilizes : ∀ (g : Behavior p m ℚ) (d : ℕ), mcMillan g = (d : ℕ∞) →
    ∃ N, ∀ n, N ≤ n → dim (run g n) = d ∧ Realizes (real (run g n)) g
  /-- I4 CONTRACTION CORRECTNESS: deflation at a simple-pole state yields a
      minimal realization of the pole-deleted behavior. (Precise simple-pole
      hypothesis packaged by the solution; weakening it is a logged defect.) -/
  deflate_minimal : ∀ (s : St) (i : Fin (dim s)),
    (real s).A.IsDiag → Function.Injective (real s).A.diag →
    (dim (deflate s i) : ℕ∞)
      = mcMillan (real (deflate s i)).behavior ∧
    dim (deflate s i) = dim s - 1

/-- **HEADLINE.** The verified self-sizing realizer EXISTS — constructively,
    hence executably. This object is the certificate; I1–I4 are its law;
    gauge (Kalman) applies to its holdings via `kalman_uniqueness`. -/
theorem selfSizer_exists (p m : ℕ) : Nonempty (VerifiedSelfSizer p m) := by
  sorry

end Realization
