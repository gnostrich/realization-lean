# TIER-STATUS — realization-lean (Agent A) — HALTED

**Work on this repository was halted by an operator scope correction on
2026-07-27.** The project scope was rewritten around the condition number
theorem (certified lower bounds on distance-to-ill-posedness) inside
`discovery-kernel`; the Kronecker/realization spine is explicitly out of
scope and this repository is not to be depended upon. Nothing below is
claimed as finished work; this file records the honest state at the halt so
nothing is lost or misrepresented.

No PR was opened. Nothing was merged to `main`. Nothing was deleted.

## Green (compiles, zero `sorry`)

* `lean/RealizationLean/Defs.lean` — the definitional layer: `shift`,
  `hankelSpace`, `shiftSpan`, `Realizes`, `IsRealizable`, `reachable`,
  `Controllable`, `obs`, `unobservable`, `Observable`, `modeSum`,
  `quadForm`, plus basic API lemmas.
* `lean/RealizationLean/Sector.lean` — **2 headlines proven**:
  `sector_decomposition` (unique symmetric ⊕ skew) and `loop_work_nullity`
  (the skew sector's quadratic form vanishes). Also `symmPart`, `skewPart`
  and their characterizations.
* `lean/RealizationLean/Kronecker.lean` — **1 headline proven**:
  `kronecker_realizable_iff` (`IsRealizable h d ↔ Hankel row space finite of
  dimension ≤ d`), with both directions and their supporting lemmas
  (`shiftOp`, `hankelShift`, `hankelState`, `hankelShift_pow_state`,
  `hankelSpace_le_range_obs`, `pad`, `pad_injective`, `dotProduct_coeffs`,
  `realizable_of_finite_of_finrank_le`).

Verified with `lake env lean <file>` against Lean `v4.32.0` / Mathlib
`v4.32.0` (packages symlinked from the sibling `discovery-kernel` checkout;
see `.lake/packages/`).

## Sorry (statement registry — `sorry` by design, but unproven here)

* `Challenge.lean` — compiles, emits exactly its 14 expected
  `declaration uses 'sorry'` warnings. It is the statement registry, so its
  `sorry`s are permanent by protocol; but of the 14 headlines only the 3
  named above have proofs anywhere in this repository. The remaining 11 are
  **stated only, not proven**:
  `rank_stabilization`, `stabilization_at_dim`, `kalman_uniqueness`,
  `kalman_dimension`, `unobservable_invisible`, `unobservability_no_go`,
  `mode_sum_hankel_rank`, `pole_deletion`, `lock_rank_not_additive`,
  `lock_no_finite_prefix_test`, `lock_kalman_needs_observability`.

## Never started

* `Solution.lean` (comparator bridge) — not written.
* `comparator` config (`config-comparator-strict.json`) — not written.
* `.github/workflows/build.yml` (build + sorry census + comparator job) —
  not written.
* `STATEMENTS.md` (verbatim statements + explicit non-claims list + the dated
  note on the deliberate `v4.32.0` pin deviation from
  `certified-positivity`'s `v4.28.0`) — not written. **The pin deviation is
  therefore recorded nowhere but here and in `SWEEP.md`.**
* `COVERAGE.md` — not written.
* `lean/RealizationLean.lean` (library root importing the modules) — not
  written; the modules were being checked individually.
* Modules for the 11 unproven headlines (`Stabilization.lean`, `Kalman.lean`,
  `Observability.lean`, `Poles.lean`, `Locks.lean`) — not written.

## Aristotle jobs left in flight (results never retrieved)

Submitted before the halt, not waited on, not fetched, not verified:

* `397e0ae0-c7f5-40ad-90a3-e33a3b2cefb1` — Kalman uniqueness
  (`∃ e : (Fin d₁ → K) ≃ₗ[K] (Fin d₂ → K)` intertwining `A`, `B`, `C` for two
  controllable+observable realizations of the same behavior).
* `1c516720-64fb-4441-a38d-fd2cd5874d03` — Hankel rank of a mode sum equals
  the number of poles (`geom_linearIndependent`, `hankelSpace_modeSum`,
  `mode_sum_hankel_rank`).

Any output from these is UNTRUSTED and unverified; it must be re-checked
locally before use anywhere.

## Note on `SWEEP.md`

`SWEEP.md` (merged to `main` as PR #2) remains accurate as a Mathlib
`v4.32.0` survey, but it surveys the realization spine, which is now out of
scope. Its transferable content is the infrastructure inventory (matrix rank,
Cayley–Hamilton, span/finiteness glue), not its spine-specific verdicts.
