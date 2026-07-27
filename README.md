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

## Layout
- `Realization/Challenge.lean` — frozen claims (tag `frozen-v1`)
- `Realization/Solution/` — proofs
- `Comparator/` — statement-match + axiom-allowlist checker
- `DIRECTIVE.md` — build instructions (CERT-LEAN-01)
- `REGISTRY.jsonl` — append-only prereg/defect/verdict log
