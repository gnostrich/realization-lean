# STATEMENTS.md — certificate spine formalization
Companion to Challenge.lean. Per standing protocol: the Lean statements ARE
the claims; this file scopes them and lists what is NOT claimed.

## Claims (verbatim = the theorem statements in Challenge.lean)

C2 spine — the certificate is provably correct in exact arithmetic:
- `kronecker_realizability` — realizable in dim d ⟺ all finite Hankel ranks ≤ d.
  (= transfer theorem T3: cost = McMillan degree, substrate-independent.)
- `growth_test_correct` — Hankel rank agreeing at two consecutive sizes has
  converged; finite test decides the infinite property. (The growth rule.)
- `kalman_uniqueness` — minimal realizations unique up to similarity.
  (= Axiom G temporal; = transfer theorem T1.)
- `unobservable_no_transfer` — interface-invisible content contributes
  nothing to behavior. (= transfer theorem T2. Executing session upgrades
  to the observable-quotient form; upgrade is REGISTRY-logged.)
- `graduation_frees_rank` — deleting one of d distinct poles (rank-1,
  nonvanishing residues) yields McMillan degree exactly d−1.

C3 regression locks — the graveyard, machine-checked:
- `schur_flag_gaming` — diag(T^k) = (diag T)^k for block-triangular T.
  Headstone of the rank–cost conservation law [proven-negative].
- `no_cost_floor` — explicit non-normal 2×2 witness realized at dim 1.

C1 calibration:
- `skew_quadratic_null`, `skew_symmetric_trace_zero` — algebraic kernel of
  Decomposition I (circulation preserves the Gibbs quadratic data).
- `transfer_defect_first_order` — first-order defect identity; formal
  autopsy of the abandoned linear-transport route.

C1' coverage-gap closers (audit 2026-07-27):
- `tilt_displaces_uniquely` — unique equilibrium under PosDef curvature;
  linear tilts displace, cannot create basins. (f_mem safety.)
- `sym_skew_unique_decomposition` — the two sectors exist, uniquely, and
  meet only at zero. (Decomposition I as fact.)
- `symmetric_loop_work_zero` — discrete loop work of any symmetric field
  vanishes on any closed polygon. (The veto's ungameability.)

## What we do NOT claim
1. Any thresholded / noisy / floor-relative criterion. All statements are
   EXACT arithmetic. The deployed test uses noise floors; its correctness
   is NOT a theorem and is not asserted as one.
2. The B-valued (operator-valued) lift. Scalar/matrix-over-a-field only.
   OV versions (MSY atomicity etc.) are Phase 2, unclaimed.
3. Anything about trained neural networks, activations, or real usage
   producing low-degree kernels (that is conjecture C-H1, empirical).
4. Off-spec generalization of re-realized behaviors (conjecture C-OS).
5. Approximate freeness of overlay families (empirical conjecture).
6. Any lower bound / conservation law for antisymmetric or non-commuting
   content. C3 exists precisely to make such claims contradict the repo.
7. The full diffusion statement of Decomposition I (measure-theoretic
   invariance under skew drift). Only its algebraic kernel is claimed.
8. Semisimple rigidity / AMNM / Hochschild vanishing theorems (cited
   context, not formalized).
9. The spatial-axis certificate (EBR anchor count = spatial McMillan
   degree). Analogical: the shared core is the temporal proof; the spatial
   Hankel/moment object is not defined in this development.
10. The coalgebraic description layer (finality, image factorization).
   Description-only; its proof-bearing shadow is `kalman_uniqueness`.
11. Any trajectory-Hankel (subspace-ID / Willems-type) rank statement.
   The deployed growth test is REALIGNED to Hankel the estimated Markov
   parameters, which the proved theorems cover; the data-Hankel shortcut
   is forbidden, not licensed. (CONFLATIONS F1.)
12. Blindness of the MAP-COMPOSITION return-residue meter (G4/membrane
   loops) to the objective sector. Proved only for field loop-work
   (`symmetric_loop_work_zero`); for return residues it is a design claim
   with the field theorem as linearized shadow. (CONFLATIONS F3.)
13. Global well-posedness / convexity of the EFFECTIVE coupled objective
   through the frozen member. Claims cover the designed quadratic model;
   contraction of the settle map is a runtime-checkable design condition,
   not a theorem. (CONFLATIONS F4.)

## Regression-lock semantics (why this is un-regressable)
- Claims cannot drift: any edit to a theorem statement breaks the
  comparator against the pinned Challenge.lean. Statement changes are
  loud, versioned REGISTRY events — never silent.
- Negatives cannot be reopened: C3 formalizes the quarantined objects as
  witnesses. A future "floor" claim added to this development contradicts
  kernel-checked theorems in the same library.
- Prose cannot overclaim: claims are enumerated here against the Lean
  names; anything not in the list is by definition not claimed.

## Execution directive (one-round, per standing testing policy)
- Session: Aristotle via CC worktree `certificate-lean`, REGISTRY prereg
  committed before first proof attempt.
- Matrix (all in one pass): C1 (expect: fast; calibration), C3 (expect:
  fast — schur_flag is triangular-diagonal algebra; witness is a concrete
  2×2), C2 (expect: hard — Hankel/realization theory absent from Mathlib;
  build from scratch, exact field arithmetic).
- Validity cell: C1 must fully close. If Aristotle cannot close C1, the
  round's verdict is "toolchain/statement repair needed", terminal for
  this round; statements return here for repair as a logged event.
- Per-theorem outcomes: PROVED / STATEMENT-DEFECT (with the defect named;
  semantic repair = REGISTRY event) / OPEN-AT-THIS-ROUND (terminal;
  recorded CLOSED-OPEN, not pending).
- Deliverable: one page — per-theorem verdict table, axiom allowlist per
  theorem (native_decide split if used), what is NOT claimed (this list),
  comparator + CI configured, pins in-repo. Push, close worktree.
- Known statement risks for the session to repair WITHOUT semantic change:
  Mathlib name drift (Matrix.rank, BlockTriangular, ℕ∞ sInf idioms),
  universe/typeclass plumbing, the Behavior-of-diagonal-entry packaging in
  `no_cost_floor`. Semantic changes (e.g. hypotheses added to make a
  theorem true) are defects, logged, and come back here.

## Block S — the headline object (added with the SelfSizing challenge)
- `VerifiedSelfSizer` + `selfSizer_exists` — an EXECUTABLE (ℚ) fold holding
  a dimension-adaptive realization with invariants: I1 soundness (matches
  all data seen), I2 minimality (dimension = Hankel rank at every step),
  I3 stabilization/coverage (degree-d source reached finitely, held
  forever, full behavior realized), I4 contraction correctness (pole
  deletion is minimal and frees exactly one dimension). The prior thirteen
  theorems are its lemma layer. Constructive proof required: over ℚ the
  proved object IS the deployable object (CONFLATIONS F1 enforced by
  construction).
- Additional non-claim 14: no claim about ESTIMATED Markov parameters —
  the object consumes exact parameters; the RLS-estimation step upstream
  remains under non-claim 1.
