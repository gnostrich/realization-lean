# DIRECTIVE.md — CERT-LEAN-01: build `realization-lean` to closure
Read fully before acting. This bundle is self-contained; do not ask the
user for clarification on anything specified here. Standing rules from the
user's program apply: REGISTRY prereg before first proof attempt;
faithful-or-wipe; statements-are-the-claims; semantic edits are logged
defects, never silent patches; negatives are first-class.

## Mission
Stand up the standalone repo `realization-lean` (owner: gnostrich; if repo
creation is blocked, work in a local worktree named `realization-lean` and
surface the push step once at the end) and drive the Challenge.lean
statements to kernel-accepted proofs, recruiting Harmonic's Aristotle
(available as the Harmonic AI MCP tool in this environment) as the prover.

## Repo contents (from this bundle, initial commit)
Challenge.lean · STATEMENTS.md · COVERAGE.md · CONFLATIONS.md ·
UNIFIED-THEORY.md · THE-OBJECT.md · README.md · REGISTRY.jsonl (create,
append-only) · lakefile + pinned Mathlib toolchain · .github/workflows/ci.yml.
Namespace is `Realization` (freeze table forbids `Certificate`).
Layout: `Realization/Challenge.lean` (frozen claims), `Realization/Solution/`
(all proof work), `Comparator/` (statement-match checker).

## Toolchain
lake new realization-lean math; pin latest stable Mathlib release tag and
matching lean-toolchain; commit pins. CI = `lake build` + comparator run.

## Stage 0 — prereg (before anything else)
Append to REGISTRY.jsonl: date, the 14 headline items (13 theorems +
selfSizer_exists), the defect protocol, the CONFLATIONS freeze table hash,
and the done-criterion from COVERAGE.md. Commit.

## Stage 1 — elaboration (statements compile, proofs stay sorry)
Repair syntax/name-drift/typeclass plumbing freely (known risks:
tilt_displaces_uniquely displacement clause; no_cost_floor packaging; ℕ∞
sInf idioms; VerifiedSelfSizer's dependent `run` default and `deflate`
signature — dependent dim rewrites may need `cast`/`HEq` handling: prefer
restating with explicit dimension equalities over HEq gymnastics, that is
a syntactic repair). ANY change to mathematical meaning = STATEMENT-DEFECT:
log to REGISTRY with the defect named, leave the theorem sorry, continue.
Deliverable: Challenge.lean elaborates under `lake build`; tag `frozen-v1`.

## Stage 2 — validity gate (Aristotle calibration)
Route to Aristotle, in order: skew_quadratic_null,
skew_symmetric_trace_zero, transfer_defect_first_order,
sym_skew_unique_decomposition, symmetric_loop_work_zero,
tilt_displaces_uniquely, schur_flag_gaming, no_cost_floor.
Aristotle protocol per theorem: submit statement + minimal context; on
returned proof run the faithfulness audit BEFORE accepting — proof proves
the exact frozen statement, no added axioms outside allowlist
(propext/Classical.choice/Quot.sound; native_decide only if unavoidable
and then split into its own allowlist entry), kernel-accepts locally.
Reject-and-retry with hints on failure; hand-finish only when Aristotle
stalls; log which. If this whole stage cannot close, verdict is
"statement repair needed" — terminal for this pass, surface to user.

## Stage 3 — the spine (C2, from-scratch library)
Build order (each a milestone commit + REGISTRY line):
1. Constructive rank factorization over a field (A = F·G, r = rank) — the
   computational heart; elimination-based; needed executable over ℚ.
2. Hankel API: shift structure, submatrix embeddings, rank monotonicity.
3. kronecker_realizability (⇐ first: realization bounds rank; then ⇒ via
   the factorization).
4. unobservable_no_transfer (+ optional quotient strengthening, logged).
5. growth_test_correct (partial-realization core: two-size rank agreement
   ⇒ stabilization; this is the load-bearing lemma for Block S I3).
6. kalman_uniqueness (via controllability/observability factor maps).
7. graduation_frees_rank (Vandermonde/partial-fraction argument).
Aristotle throughout: decompose into lemma-sized requests; never submit a
milestone whole. Per-theorem outcomes: PROVED / STATEMENT-DEFECT /
OPEN-AT-THIS-PASS (terminal, logged, move on).

## Stage 4 — Block S (the headline object)
Construct the witness for selfSizer_exists over ℚ:
- St = Σ d, (Real p m d ℚ × certificate data: current Hankel factorization
  + last two rank readings).
- step: check whether the new parameter is consistent with the held
  realization's prediction; if yes, state unchanged (certificate data
  updated); if no, re-factorize the enlarged Hankel and Ho–Kalman a
  realization of the new rank.
- deflate: delete the indexed pole (diagonal case per the field's
  hypotheses).
- Prove I1 (soundness), I2 (minimality), I3 (stabilization — reuses
  growth_test_correct), I4 (deflate_minimal — reuses
  graduation_frees_rank). Executability: prefer `decide`-free constructive
  definitions; a small #eval smoke on a degree-2 toy behavior goes in
  `Realization/Solution/Demo.lean` (not a claim, a sanity artifact).

## Stage 5 — comparator + CI
Comparator: checks Solution proves statements syntactically identical to
frozen-v1 Challenge.lean (modulo proof terms), reports per-theorem axiom
sets against the allowlist. CI: lake build + comparator on every push.
Done-criterion (from COVERAGE.md): every [T] kernel-accepted ∧ comparator
green ∧ CI green.

## Reporting
One page per completed stage appended to PROGRESS.md: verdict table
(theorem | status | axioms | Aristotle-or-hand), defects logged, nothing
else. No partial chatter to the user between stages. Final deliverable:
repo pushed, tags frozen-v1 and closed-v1 (if reached), PROGRESS.md
complete, REGISTRY complete.

## Boundaries (do not cross)
- Never edit frozen statements to make them provable without logging.
- Never claim anything in the STATEMENTS.md non-claims list (1–14).
- Naming per CONFLATIONS.md freeze table, in code and comments.
- No experiments, no models, no empirical anything — this is build work.
