# realization-lean

Finite-dimensional linear realization theory in Lean 4 — Kronecker
realizability, rank stabilization, Kalman uniqueness, the unobservability
no-go, pole deletion, sector decomposition, and machine-checked
counterexample locks — culminating in a **verified, executable,
self-sizing realization**: the certificate as a single object
(`VerifiedSelfSizer`), whose invariants are soundness, step-wise
minimality, finite stabilization with full coverage, and
contraction-correct pole deletion.

Protocol: `Challenge.lean` fixes the exact claimed statements — the
statements are the claims; `STATEMENTS.md` scopes them and lists what is
NOT claimed (fourteen explicit non-claims); `COVERAGE.md` maps every
statement of `UNIFIED-THEORY.md` to a theorem, a non-claim, or a
definition; `CONFLATIONS.md` freezes the vocabulary. A comparator
verifies any solution against the frozen challenge; CI runs the build and
comparator continuously.

This library is the shared formal core of several downstream systems,
which cite it; it makes no claims about any of them.

## Motivation

Models are typically deployed frozen. We posit that whatever they should
learn from use can live in an overlay harness — not a wrapper around the
model but a modifier sharing its shape: additive or multiplicative
overlays on the individual weights (and, optionally, activations),
structured by the same depths and channels as the model itself. That
inherited shape is what lets influence genuinely travel inward —
accumulated use biases the computation where it happens, the way a
conversation shapes a listener without rewiring the brain. Things we'd
hope for from such a layer: depth of influence without weight edits to
the underlying model; harnesses transferable across instances or agents
of the same model, so that learning can accumulate collectively rather
than per-session; and, more wishfully, across different models altogether
— where internals aren't shared, so only the interface description of a
behavior travels and is rebuilt natively on the other side, like
teaching. We take the interface as given (port types and correspondence
fixed in advance, the way people inherit a language rather than
negotiating one). Under that assumption one classical theory governs all
of it: interface behavior determines internal realization up to
coordinates; what never reaches the interface cannot be carried; a
behavior is rebuildable wherever capacity meets its complexity; and the
layer should grow exactly when its history certifiably exceeds its size,
and make a piece permanent exactly when it has certifiably stopped
changing — finite tests, and theorems. This repository formalizes that
spine as one executable object: a verified self-sizing realization.
(Cross-modal is not a separate case — given typing, another modality is
just more ports. Typing discovery is real and deliberately out of scope;
the framework leaves that door open.)

Formal development of finite-dimensional linear realization theory:
Kronecker's theorem (Hankel rank ⟺ realizability in dimension d), rank
stabilization (a finite test decides minimality), Kalman uniqueness
(minimal realizations are similar — internal coordinates are gauge), the
unobservability no-go (interface-invisible state cannot affect behavior),
pole deletion (removing one of d distinct poles yields degree exactly
d−1), and the unique symmetric ⊕ skew decomposition with its loop-work
nullity. The development also carries machine-checked counterexample
locks: formalized witnesses that certain conservation-law-shaped claims
are false, making their reintroduction contradict the library.

## Proof status (read this before citing anything)

"Proved" here means **kernel-accepted with no `sorry` anywhere in its
dependency cone**, axioms within {`propext`, `Classical.choice`,
`Quot.sound`}. `lake exe comparator` is the authority; it reports three
distinct states and must not be read as a pass/fail.

- **PROVED (9):** `unobservable_no_transfer`, `skew_quadratic_null`,
  `skew_symmetric_trace_zero`, `transfer_defect_first_order`,
  `sym_skew_unique_decomposition`, `tilt_displaces_uniquely`,
  `symmetric_loop_work_zero`, `schur_flag_gaming`, `no_cost_floor`.
  Plus the whole of `Solution/Basic.lean` (Hankel API) and
  `Solution/Defects.lean`.
- **REDUCED, NOT PROVED (3):** `kronecker_realizability`,
  `kalman_uniqueness`, `selfSizer_exists`. Each has a complete argument
  in the repository, but each rests on unproved master lemmas — the
  seven `sorry`s in `Solution/StateSpace.lean` and
  `exists_partial_realization` in `Solution/PartialRealization.lean`.
  They are reductions to those lemmas, not theorems. Do not cite them as
  proved.
- **STATEMENT-DEFECT (1):** `growth_test_correct` is **false as frozen**
  and stays `sorry`. Its refutation is kernel-checked in
  `Solution/Defects.lean`. See below.

So the C2 spine is **4 claims, not 5**, and 3 of the 4 are conditional at
this pass.

### `growth_test_correct` is false

Its hypotheses constrain only `g 0 … g (2r+2)` while its conclusion
quantifies over every window and over `mcMillan g`, which depend on the
unconstrained tail. Witness (`r = 0`, `p = m = 1`, `𝕜 = ℚ`): `g k = 0`
for `k ≤ 2`, `g 3 = 1`. Both hypothesis Hankels vanish; the conclusion
fails at `n = 3`. Kernel-checked as
`Realization.Solution.growth_test_correct_is_false`.

Consequence: `mcMillan g = r` is **not** available downstream from a
two-window test, and the deployed growth test has no theorem behind it
(on top of the CONFLATIONS F1 realignment). The repair needs an
a-priori realizability/finite-degree hypothesis — classical rank
stabilization presupposes the sequence is C-finite; two windows cannot
establish it. The true statement proved here is
`hankel_rank_eq_of_mcMillan` (`Solution/Kronecker.lean`):
`mcMillan g = d → ∀ n ≥ d, (hankel g n).rank = d`. Re-freezing the
statement is the claim owner's call and is logged as a pending
STATEMENT-DEFECT repair in `REGISTRY.jsonl`.

## Layout
- `Realization/Challenge.lean` — frozen claims (tag `frozen-v1`)
- `Realization/Solution/` — proofs
- `Comparator/` — statement-match + axiom-allowlist checker
- `DIRECTIVE.md` — build instructions (CERT-LEAN-01)
- `REGISTRY.jsonl` — append-only prereg/defect/verdict log
- `SWEEP.md` — Mathlib sweep verdicts for the spine
- `TIER-STATUS.md` — tier status

## Toolchain

Pinned to Lean `leanprover/lean4:v4.28.0` and Mathlib `v4.28.0`. This is
the toolchain Harmonic's Aristotle reports as its expected version, and
Aristotle is the prover driving `Realization/Solution/`; every proof in
this repository is kernel-checked against these pins. `SWEEP.md` was
written against `v4.32.0` and its lemma verdicts carry over — its
toolchain line is superseded by this pin (logged in `REGISTRY.jsonl`).
