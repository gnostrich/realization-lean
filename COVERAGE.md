# COVERAGE.md — total map: theory → formal status
The done-criterion instrument. Every substantive line of UNIFIED-THEORY.md
maps to exactly ONE of: a Challenge.lean theorem name [T], a STATEMENTS.md
non-claim number [N], or DEFINITIONAL [D] (a naming/identification that has
no proof content by nature). DONE ⟺ this table is total ∧ every [T] row is
kernel-accepted ∧ comparator + CI green. A theory edit that adds a row
without an assignment breaks doneness — loudly.

(Same pattern as the ITP paper's verified coverage theorem, applied to the
theory document itself: a finite certificate that the stated object is
covered.)

| theory statement | status |
|---|---|
| Axiom G, temporal appearance (Kalman uniqueness) | [T] kalman_uniqueness |
| Axiom G, spatial appearance (invariant-interface rule) | [D] design axiom; proof-bearing shadow = kalman_uniqueness |
| Axiom G, across-systems (transfer = re-realization) | [T] kalman_uniqueness + kronecker_realizability |
| Axiom G, across-agents (human communication) | [D] existence motivation, not a claim |
| Statics: unique equilibrium; tilt displaces, cannot create basins | [T] tilt_displaces_uniquely |
| Gibbs measure form; temperature semantics | [N] 7 (diffusion/measure theory not claimed) |
| Decomposition I exists & is unique; sectors meet at 0 | [T] sym_skew_unique_decomposition |
| Circulation preserves the objective's quadratic data | [T] skew_quadratic_null, skew_symmetric_trace_zero |
| Full invariant-measure preservation under skew drift | [N] 7 |
| Verdict principle: LOOP WORK blind to objective sector | [T] symmetric_loop_work_zero |
| Return-residue meter (G4/membrane) blind to objective | [N] 12 (design claim; field theorem = linearized shadow) |
| Free-lunch principle (pressure lands in gradient sector) | [D] corollary-form of the split; no separate proof content |
| Statics of the DESIGNED quadratic model | [T] tilt_displaces_uniquely |
| Well-posedness of the EFFECTIVE coupled objective | [N] 13 (runtime design condition, not a theorem) |
| Deployed growth test (Markov-param Hankel of RLS estimates) | [T] growth_test_correct after F1 realignment |
| Trajectory-Hankel shortcut | [N] 11 (forbidden, not licensed) |
| Deployed graduation gate (pole-stationarity test) | [N] 1 (noisy criterion; "atom" reserved per F2) |
| Empirical McMillan degree (population object in C-H1) | [N] 3 (defined conjecture-side per F5) |
| Decomposition II: MZ kernel = B-valued resolvent | [N] 2 (OV lift not claimed; scalar shadow below) |
| Finite Hankel rank ⟺ rational ⟺ atomic (scalar) | [T] kronecker_realizability |
| Finite test decides infinite property (growth rule) | [T] growth_test_correct |
| Three media = three spectral regions | [D] naming of pole regions; λ=1 ⇒ constant is arithmetic |
| Graduation = boundary pole retired; frees exactly one rank | [T] graduation_frees_rank |
| Graduation veto must be loop-side | [T] symmetric_loop_work_zero (why) + [D] design placement |
| Transfer T1 (uniqueness up to gauge) | [T] kalman_uniqueness |
| Transfer T2 (unobservable content cannot cross) | [T] unobservable_no_transfer |
| Transfer T3 (cost = McMillan degree) | [T] kronecker_realizability |
| Composition safe under re-realization | [D] on-spec exactness is by construction; off-spec = [N] 4 |
| Hochschild defect (abandoned route autopsy) | [T] transfer_defect_first_order |
| Amenability / AMNM / HH² context | [N] 8 |
| Rank–cost floor is false (Schur-flag) | [T] schur_flag_gaming |
| No transfer-cost floor (witness) | [T] no_cost_floor |
| One certificate, spatial axis (EBR anchors) | [N] 9 (NEW: analogical; spatial Hankel object not defined here) |
| Coalgebraic description (finality, factorization) | [N] 10 (NEW: description-only; shadow = kalman_uniqueness) |
| Thresholded/noisy criterion correctness | [N] 1 |
| B-valued lift (MSY atomicity) | [N] 2 |
| Real usage yields low-degree kernels | [N] 3 (= conjecture C-H1) |
| Off-spec generalization | [N] 4 (= conjecture C-OS) |
| Approximate freeness of overlay families | [N] 5 |
| Any antisymmetric conservation law | [N] 6 + contradicted by C3 locks |
| Ω register jobs (route/sensor/veto) | [D] imported machinery + design placement; killed drift cell noted in THE-OBJECT |
| Switches (frame/substrate/modality) | [D] design calculus over the theorems above |

Rows: 41 after conflation splits (CONFLATIONS.md F1–F5). [T]: 15 row-
assignments over 13 named theorems. [N]: 18 assignments over 13 non-claims
(11–13 added by the conflation audit). [D]: 8. Unassigned: 0 — total as of
2026-07-27, post-conflation-check.

REMAINING FOR DONE: every [T] kernel-accepted; comparator pinned to the
frozen Challenge.lean; CI green; non-claims 9 and 10 added to STATEMENTS.md
(done below in this commit's companion edit).

Maintenance rule: any edit to UNIFIED-THEORY.md must add/modify a row here
in the same commit, or the edit is a regression by definition.

## Block S rows (SelfSizing headline)
| The certificate as one object (grow/deflate constructors) | [T] VerifiedSelfSizer / selfSizer_exists |
| Grow on certified novelty, never oversized | [T] fields sound, minimal |
| Finite certificate covers infinite behavior | [T] field stabilizes (I3) |
| Graduation as machine step, frees one dimension | [T] field deflate_minimal (I4) |
| Runs on estimated parameters | [N] 14 (exact-input object; estimation upstream = [N]1) |
Updated tallies: +5 rows; unassigned remains 0.
