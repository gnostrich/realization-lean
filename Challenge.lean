import Mathlib

/-!
# Challenge.lean — Mathlib-only statements of the headline theorems

This file states, with `sorry` as every proof, the headline theorems of this
repository. It imports **only Mathlib** — no repository modules — and inlines
every definition the statements need, copied verbatim from the named source
files (see the `-- from <file>` markers). Its purpose is mechanical: the
statements here can be compared against the repository modules (with a
statement comparator) to check that the sorry-free proofs in `lean/` prove
exactly these claims and not something subtly different.

Toolchain: `leanprover/lean4:v4.32.0`, Mathlib `v4.32.0` (as pinned by
`lean-toolchain` / `lakefile.toml` / `lake-manifest.json` at the repo root).

Because all definitions live here in the single namespace `Challenge`, the
namespace prefixes of the originals (`RealizationLean.`) are necessarily
dropped; this is the one systematic transformation applied to every inlined
definition and statement.

This file makes **no axiom claim**: every proof below is `sorry`, so
`#print axioms` on this file is meaningless by design. Axiom status of the
real proofs is a property of the repository modules, not of this file.

The reading of the objects (fixed once, used everywhere below): a sequence
`h : ℕ → K` is an *interface behavior* — its `k`-th value is the `k`-th
Markov parameter of a linear system. A *realization* of dimension `d` is an
internal state machine `(A, B, C)` producing that behavior. The theorems say:
interface behavior determines internal realization up to coordinates
(`kalman_uniqueness`), a behavior is realizable exactly when its Hankel rank
is finite and small enough (`kronecker_realizable_iff`), that rank is decided
by a finite test (`rank_stabilization`, `stabilization_at_dim`), and what
never reaches the interface cannot be carried (`unobservability_no_go`).
-/

open scoped Matrix

namespace Challenge

/-! ## Definitions — from `lean/RealizationLean/Defs.lean`
(namespace `RealizationLean`) -/

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

/-! ## Definitions — from `lean/RealizationLean/Sector.lean`
(namespace `RealizationLean`) -/

/-- The quadratic form `xᵀ M x`; over ℝ, the "work" of the field `M` along
`x`. -/
def quadForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * M i j * x j

/-! ## Headline theorems, stated with `sorry`
Sorry-free proofs live in the named repository modules. -/

/-! ### 1. Kronecker realizability -/

/-- **Kronecker realizability.** An interface behavior is realizable by a
`d`-dimensional state machine exactly when its Hankel rank is finite and at
most `d`. Behavior determines the size of the machine that can carry it. -/
theorem kronecker_realizable_iff {K : Type*} [Field K] (h : ℕ → K) (d : ℕ) :
    IsRealizable h d ↔
      Module.Finite K (hankelSpace h) ∧ Module.finrank K (hankelSpace h) ≤ d := by
  sorry

/-! ### 2. Rank stabilization: a finite test decides minimality -/

/-- **Rank stabilization, sufficiency.** One repeat certifies the whole
infinite chain: if the span of the first `n + 1` shifts equals the span of the
first `n`, then it already is the full Hankel row space. -/
theorem rank_stabilization {K : Type*} [Field K] (h : ℕ → K) (n : ℕ)
    (hstab : shiftSpan h (n + 1) = shiftSpan h n) :
    hankelSpace h = shiftSpan h n := by
  sorry

/-- **Rank stabilization, completeness.** The test never has to be run past the
realization dimension: a behavior realizable in dimension `d` stabilizes at
step `d`. Together with `rank_stabilization`, testing one equality at step `d`
decides the Hankel rank, hence minimality. -/
theorem stabilization_at_dim {K : Type*} [Field K] (h : ℕ → K) (d : ℕ)
    (hd : IsRealizable h d) :
    shiftSpan h (d + 1) = shiftSpan h d := by
  sorry

/-! ### 3. Kalman uniqueness: internal coordinates are gauge -/

/-- **Kalman uniqueness.** Two minimal (controllable and observable)
realizations of the same interface behavior are related by an invertible
change of internal coordinates intertwining the dynamics, the input port and
the output port. Internal coordinates carry no information the interface does
not already fix. -/
theorem kalman_uniqueness {K : Type*} [Field K] {d₁ d₂ : ℕ} (h : ℕ → K)
    (A₁ : Matrix (Fin d₁) (Fin d₁) K) (B₁ C₁ : Fin d₁ → K)
    (A₂ : Matrix (Fin d₂) (Fin d₂) K) (B₂ C₂ : Fin d₂ → K)
    (hr₁ : Realizes h A₁ B₁ C₁) (hr₂ : Realizes h A₂ B₂ C₂)
    (hc₁ : Controllable A₁ B₁) (ho₁ : Observable A₁ C₁)
    (hc₂ : Controllable A₂ B₂) (ho₂ : Observable A₂ C₂) :
    ∃ e : (Fin d₁ → K) ≃ₗ[K] (Fin d₂ → K),
      (∀ x, e (A₁ *ᵥ x) = A₂ *ᵥ e x) ∧ e B₁ = B₂ ∧ ∀ x, C₂ ⬝ᵥ e x = C₁ ⬝ᵥ x := by
  sorry

/-- **Kalman uniqueness, dimension corollary.** Minimal realizations of the
same behavior all have the same dimension. -/
theorem kalman_dimension {K : Type*} [Field K] {d₁ d₂ : ℕ} (h : ℕ → K)
    (A₁ : Matrix (Fin d₁) (Fin d₁) K) (B₁ C₁ : Fin d₁ → K)
    (A₂ : Matrix (Fin d₂) (Fin d₂) K) (B₂ C₂ : Fin d₂ → K)
    (hr₁ : Realizes h A₁ B₁ C₁) (hr₂ : Realizes h A₂ B₂ C₂)
    (hc₁ : Controllable A₁ B₁) (ho₁ : Observable A₁ C₁)
    (hc₂ : Controllable A₂ B₂) (ho₂ : Observable A₂ C₂) :
    d₁ = d₂ := by
  sorry

/-! ### 4. The unobservability no-go -/

/-- **Interface-invisible state is inert.** Perturbing the input port by an
unobservable state does not change a single Markov parameter: what never
reaches the interface cannot be carried. -/
theorem unobservable_invisible {K : Type*} [Field K] {d : ℕ} (h : ℕ → K)
    (A : Matrix (Fin d) (Fin d) K) (B C : Fin d → K) (hr : Realizes h A B C)
    (x : Fin d → K) (hx : x ∈ unobservable A C) :
    Realizes h A (B + x) C := by
  sorry

/-- **The unobservability no-go.** A realization with any interface-invisible
state is never minimal: the same behavior is already carried by a strictly
smaller machine. -/
theorem unobservability_no_go {K : Type*} [Field K] {d : ℕ} (h : ℕ → K)
    (A : Matrix (Fin d) (Fin d) K) (B C : Fin d → K) (hr : Realizes h A B C)
    (hu : unobservable A C ≠ ⊥) :
    ∃ d' < d, IsRealizable h d' := by
  sorry

/-! ### 5. Pole deletion -/

/-- **Mode sums have exactly as many dimensions as poles.** A sum of `d`
geometric modes with distinct nonzero poles and nonzero residues has Hankel
rank exactly `d`. -/
theorem mode_sum_hankel_rank {K : Type*} [Field K] (s : Finset K) (c : K → K)
    (h0 : ∀ p ∈ s, p ≠ 0) (hc : ∀ p ∈ s, c p ≠ 0) :
    Module.Finite K (hankelSpace (modeSum s c)) ∧
      Module.finrank K (hankelSpace (modeSum s c)) = s.card := by
  sorry

/-- **Pole deletion.** Deleting one of `d` distinct poles yields a behavior of
Hankel rank exactly `d - 1`: no cancellation, no collapse — the deleted mode
costs exactly one dimension. -/
theorem pole_deletion {K : Type*} [Field K] [DecidableEq K] (s : Finset K) (c : K → K)
    (h0 : ∀ p ∈ s, p ≠ 0) (hc : ∀ p ∈ s, c p ≠ 0) (q : K) (hq : q ∈ s) :
    Module.finrank K (hankelSpace (modeSum (s.erase q) c)) + 1 = s.card := by
  sorry

/-! ### 6. Sector decomposition and loop-work nullity -/

/-- **Unique symmetric ⊕ skew decomposition.** Every square real matrix splits
uniquely into a symmetric and a skew part. -/
theorem sector_decomposition {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    ∃! P : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ,
      P.1ᵀ = P.1 ∧ P.2ᵀ = -P.2 ∧ M = P.1 + P.2 := by
  sorry

/-- **Loop-work nullity.** The skew sector does no work: its quadratic form
vanishes identically. -/
theorem loop_work_nullity {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (hW : Wᵀ = -W)
    (x : Fin n → ℝ) :
    quadForm W x = 0 := by
  sorry

/-! ### 7. Counterexample locks
Machine-checked witnesses that conservation-law-shaped claims about this
theory are FALSE. Their point is negative: reintroducing any of these claims
contradicts the library. -/

/-- **Lock: Hankel rank is not additive.** Dimension is not a conserved
quantity under superposition of behaviors — two rank-one behaviors can cancel
to rank zero. -/
theorem lock_rank_not_additive :
    ¬ ∀ h₁ h₂ : ℕ → ℚ,
        Module.finrank ℚ (hankelSpace (h₁ + h₂)) =
          Module.finrank ℚ (hankelSpace h₁) + Module.finrank ℚ (hankelSpace h₂) := by
  sorry

/-- **Lock: no finite prefix of the interface decides the dimension.** For
every horizon `N` there are two behaviors agreeing on the first `N` Markov
parameters, one realizable in dimension `0` and one not. The stabilization
certificate of `rank_stabilization` — not the length of the observed prefix —
is what licenses a rank verdict. -/
theorem lock_no_finite_prefix_test (N : ℕ) :
    ∃ h₁ h₂ : ℕ → ℚ, (∀ k < N, h₁ k = h₂ k) ∧
      IsRealizable h₁ 0 ∧ ¬ IsRealizable h₂ 0 := by
  sorry

/-- **Lock: controllability alone does not make coordinates gauge.** Kalman
uniqueness genuinely needs observability: there are two controllable
realizations of the same behavior, of the same dimension, that no change of
coordinates relates. -/
theorem lock_kalman_needs_observability :
    ∃ (h : ℕ → ℚ) (A₁ : Matrix (Fin 1) (Fin 1) ℚ) (B₁ C₁ : Fin 1 → ℚ)
      (A₂ : Matrix (Fin 1) (Fin 1) ℚ) (B₂ C₂ : Fin 1 → ℚ),
      Realizes h A₁ B₁ C₁ ∧ Realizes h A₂ B₂ C₂ ∧
        Controllable A₁ B₁ ∧ Controllable A₂ B₂ ∧
        ¬ ∃ e : (Fin 1 → ℚ) ≃ₗ[ℚ] (Fin 1 → ℚ),
            (∀ x, e (A₁ *ᵥ x) = A₂ *ᵥ e x) ∧ e B₁ = B₂ ∧ ∀ x, C₂ ⬝ᵥ e x = C₁ ⬝ᵥ x := by
  sorry

end Challenge
