# SWEEP.md — Mathlib sweep for the realization-lean spine

Hour-one blocker deliverable. Swept Mathlib `v4.32.0` (local olean cache at
`/home/user/discovery-kernel/.lake/packages/mathlib`, the pinned toolchain of
this repo) for every ingredient of the spine fixed by README.md. One verdict
per needed lemma:

* **CITE(`Name`)** — exists in Mathlib, use directly (file noted).
* **PORT** — a nearby Mathlib result covers most of it; wrap/adapt.
* **BUILD** — absent from Mathlib; prove in this repository.

Toolchain note (deliberate deviation from prior art): the mirrored repo
`certified-positivity` pins Lean/Mathlib `v4.28.0`; **this repo pins
`v4.32.0`** (Lean `leanprover/lean4:v4.32.0`, Mathlib `v4.32.0`) to reuse the
locally cached toolchain of the sibling `discovery-kernels` checkout. To be
recorded in STATEMENTS.md when the skeleton lands (step 2).

## Global verdict

Mathlib has **no realization theory, no control theory, no Hankel matrices,
no C-finite/exponential-polynomial sequence theory** (`grep -ri
"controllab|observab|kalman|realization|hankel"` over `Mathlib/` returns
only unrelated hits). Every *theorem* of the spine is **BUILD**. All the
*infrastructure* (linear algebra over fields, Cayley–Hamilton, matrix rank,
power series and polynomial coefficient calculus, Vandermonde, rational
function fields, kernel-chain stabilization) is **CITE**. Detail per spine
item follows.

## 1. Kronecker realizability (Hankel rank ⟺ realizability in dimension d)

Target shape: `h : ℕ → K` moment sequence; `∃ (A : Matrix (Fin d) (Fin d) K)
(B : Fin d → K) (C : Fin d → K), ∀ k, h k = C ⬝ᵥ (A ^ k) *ᵥ B` iff the span
of the shifts of `h` (row space of the infinite Hankel matrix) has dimension
≤ d. Equivalent bridges: linear recurrence of order d; rational generating
function with denominator degree ≤ d.

* Hankel matrix / Hankel rank: **BUILD** (define row space as
  `Submodule.span K (Set.range fun i => fun j => h (i + j))`).
* Realizability predicate `h k = C·Aᵏ·B`: **BUILD** (definition only;
  `Matrix.mulVec`, `dotProduct`, `Matrix.pow` all CITE).
* Rank → recurrence (shift endomorphism has annihilating polynomial):
  **CITE(`LinearMap.aeval_self_charpoly`, `LinearMap.charpoly_monic`,
  `LinearMap.charpoly_natDegree`)** — `Mathlib/LinearAlgebra/Charpoly/
  Basic.lean` (Cayley–Hamilton for `Module.Finite + Module.Free`, automatic
  over a field); restriction machinery **CITE(`LinearMap.restrict`,
  `LinearMap.restrict_apply`, `Submodule.map_span`, `Submodule.span_le`)**;
  `Polynomial.aeval_eq_sum_range` for expanding the annihilator.
* Recurrence → rank (shifts spanned by first d shifts): **BUILD** (strong
  induction); finiteness glue **CITE(`Submodule.fg_span`,
  `Module.Finite.iff_fg` — `Mathlib/RingTheory/Finiteness/Basic.lean:331`,
  `Submodule.finiteDimensional_of_le` —
  `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean:195`)**.
* Recurrence → realization in companion form: **BUILD** (companion matrix of
  the recurrence; Mathlib has `Matrix.charpoly` but **no companion-matrix
  realization lemma**; `LinearRecurrence` in
  `Mathlib/Algebra/LinearRecurrence.lean` has `IsSolution`, `solSpace`,
  `toInit`, `charPoly`, `geom_sol_iff_root_charPoly` and explicitly *no*
  closed forms — nothing to cite beyond the definition, which we can mirror
  with a plain `∃ d c, ∀ n, h (n + d) = ∑ i, c i * h (n + i)`).
* Realization → recurrence (Cayley–Hamilton on `A`):
  **CITE(`Matrix.aeval_self_charpoly`, `Matrix.charpoly_monic`,
  `Matrix.charpoly_natDegree_eq_dim`)** —
  `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean`, `Coeff.lean`.
* Generating-function bridge (optional headline): polynomial ↪ power series
  **CITE(`Polynomial.coeff_coe`, `Polynomial.coe_mul`,
  `Polynomial.coeToPowerSeries.ringHom`, `PowerSeries.coeff_mul`,
  `PowerSeries.coeff_X_pow_mul'`, `PowerSeries.trunc`,
  `PowerSeries.coeff_trunc`)**; antidiagonal calculus
  **CITE(`Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`,
  `Finset.sum_range_reflect`, `Finset.sum_range_succ'`)**. The equivalence
  itself: **BUILD**.

## 2. Rank stabilization (finite test decides minimality)

Target: the rank of the d×d truncated Hankel/controllability data stabilizes
— one equality of successive finite ranks certifies the infinite rank; the
minimal realization dimension is computable by a finite test.

* Finite truncation rank: **CITE(`Matrix.rank`,
  `Matrix.rank_eq_finrank_span_cols`, `Matrix.rank_eq_finrank_span_row`,
  `Matrix.rank_mul_le`)** — `Mathlib/LinearAlgebra/Matrix/Rank.lean`.
* Chain-stabilization engine: **CITE(`LinearMap.ker_pow_constant` —
  `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean:662`,
  `LinearMap.exists_ker_pow_eq_ker_pow_succ`,
  `LinearMap.ker_pow_eq_ker_pow_finrank_of_le` —
  `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`)**; same pattern for
  image/span chains via `Submodule` lattice + `Module.finrank` monotonicity
  (**CITE(`Submodule.finrank_le_finrank_of_le`/`Submodule.finrank_mono`,
  `Submodule.eq_of_le_of_finrank_le`)**).
* "Span of shifts up to d determines all shifts once stable": **BUILD**
  (Krylov-style argument, the workhorse of item 1's recurrence direction —
  shared lemma).
* Stabilized finite rank = infinite Hankel rank = minimal realization
  dimension: **BUILD**.

## 3. Kalman uniqueness (minimal realizations are similar)

Target: two realizations of the same `h`, both of minimal dimension d, are
related by a (unique) change of basis `T` with `A' = T A T⁻¹`, `B' = T B`,
`C' = C T⁻¹`.

* Everything specific: **BUILD**. Mathlib has no controllability/
  observability matrices, no gramians, no similarity-of-realizations
  results.
* Infrastructure: **CITE(`Matrix.toLin'`, `LinearMap.toMatrix'`,
  `Matrix.vandermonde`/`Matrix.det_vandermonde` —
  `Mathlib/LinearAlgebra/Vandermonde.lean` — for distinct-pole special
  cases, `Matrix.fromBlocks` — `Mathlib/Data/Matrix/Block.lean`,
  `LinearMap.finrank_range_add_finrank_ker` (rank–nullity),
  `LinearEquiv.ofBijective`)**. Surjective/injective from rank-d
  controllability/observability factorizations: rank–nullity + `Matrix.rank`
  API above.

## 4. Unobservability no-go (interface-invisible state cannot affect behavior)

Target: if a state vector lies in the unobservable subspace (kills `C·Aᵏ`
for all k), it contributes nothing to the interface sequence; equivalently
behavior factors through the observable quotient.

* Unobservable subspace `⨅ k, ker (C ∘ Aᵏ)`: **BUILD** (definition);
  `Submodule` infima/quotients **CITE(`Submodule.iInf`, `Submodule.mapQ`,
  `Submodule.Quotient` API)**.
* Invariance of the unobservable subspace under `A` and the finite cutoff
  (`⨅ k < d` suffices, by Cayley–Hamilton): **BUILD**, using item 1's CITEs.
* The no-go itself (quotient realization has identical interface behavior):
  **BUILD** — pure linear algebra, no Mathlib counterpart.

## 5. Pole deletion (removing one of d distinct poles drops degree to exactly d−1)

Target: transfer function with d distinct poles (partial-fractions normal
form `∑ i, cᵢ/(z − pᵢ)`, all residues nonzero); deleting one summand yields
McMillan degree exactly d−1.

* Rational function field: **CITE(`RatFunc` — `Mathlib/FieldTheory/RatFunc/
  {Defs,Basic,Degree}.lean`; `RatFunc.num`, `RatFunc.denom`,
  `RatFunc.num_div_denom`, `RatFunc.intDegree`)**.
* Partial fractions: **CITE/PORT(`div_eq_quo_add_rem_div_add_rem_div`,
  `div_prod_eq_quo_add_sum_rem_div` —
  `Mathlib/Algebra/Polynomial/PartialFractions.lean`)** — existence over a
  field of fractions is there; uniqueness lemmas
  (`quo_add_sum_rem_div_unique`) also there. What's missing:
  degree-of-a-sum-with-distinct-poles bookkeeping — **BUILD**.
* "Degree exactly d−1" (no cancellation because the remaining residues are
  nonzero): **BUILD**; distinct-linear-denominators coprimality
  **CITE(`Polynomial.isCoprime_X_sub_C_of_ne` (or
  `Polynomial.pairwise_coprime_X_sub_C`) —
  `Mathlib/Algebra/Polynomial/Splits.lean`/`RingDivision`)**.
* Equivalent sequence-side form (mode sums `n ↦ cᵢ·pᵢⁿ`, Hankel rank exactly
  d via Vandermonde): **BUILD** with
  **CITE(`Matrix.det_vandermonde`)** — this form avoids `RatFunc` entirely
  and is the recommended headline shape (matches the Hankel ontology of
  item 1).

## 6. Symmetric ⊕ skew decomposition, loop-work nullity

Target: unique decomposition `M = S + W`, `Sᵀ = S`, `Wᵀ = −W` (char ≠ 2);
the skew part is exactly the obstruction to path-independent "work", and the
quadratic form of `W` vanishes (`xᵀWx = 0` — loop-work nullity).

* Symmetry predicate: **CITE(`Matrix.IsSymm` —
  `Mathlib/LinearAlgebra/Matrix/Symmetric.lean`)**; skew: Mathlib's
  `Matrix.IsSkewAdjoint` lives in the Lie-algebra layer
  (`Mathlib/Algebra/Lie/SkewAdjoint.lean`) — simpler to **BUILD** a local
  `Mᵀ = −M` predicate (or state with the equation inline, mirroring
  `certified-positivity`'s inline `Mᵀ = M` style).
* Existence/uniqueness of the decomposition (`S = (M + Mᵀ)/2`,
  `W = (M − Mᵀ)/2`): **BUILD** — elementary; no direct Mathlib lemma for
  matrices (the bilinear-form analogue `LinearMap.IsSymm`/`IsAlt` exists but
  porting costs more than the 10-line direct proof).
* Loop-work nullity `xᵀWx = 0` for skew `W`: **BUILD** (one-liner from
  transpose of a scalar); quadratic-form vocabulary mirrored from prior art
  (`quadForm` in `certified-positivity/lean/Horizon.lean`), not from Mathlib.

## 7. Counterexample locks

Formalized witnesses that conservation-law-shaped claims are false. By
construction these are **BUILD** (each lock is a concrete finite matrix /
sequence with a `decide`/`norm_num`-level refutation; `Matrix.of
![![...]]` notation and `Matrix.mulVec` CITE'd from Mathlib). No
`native_decide` — the prior-art strict comparator allowlist
(`propext`, `Quot.sound`, `Classical.choice`) is the target for **all**
headlines, locks included.

## Cross-cutting infrastructure (all CITE, verified present in v4.32.0)

* `Matrix.pow`, `Matrix.mulVec`, `dotProduct`, `Matrix.transpose` API.
* `Module.finrank`, `FiniteDimensional`, `Submodule.span` +
  `Submodule.mem_span` elimination lemmas.
* `Fin.sum_univ_eq_sum_range`, `Finset.sum_apply`, big-operator calculus.
* `Polynomial.degree_sub_lt` (leading-cancellation), `Polynomial.Monic` API,
  `Polynomial.eq_zero_of_infinite_isRoot` (char-0 vanishing arguments),
  `IsAlgClosed.exists_root`, `Polynomial.dvd_iff_isRoot`.
* Geometric/`invUnitsSub`/`invOneSubPow` power-series identities
  (`Mathlib/RingTheory/PowerSeries/WellKnown.lean`) if the GF bridge is
  used.

## Non-Mathlib prior art

`/workspace/certified-positivity` (frozen, read-only): protocol templates
(Challenge/Solution/comparator configs/CI/STATEMENTS/coverage ledger) are
mirrored, not its mathematics. Its `quadForm`/`IsPDq` vocabulary is reused
verbatim where the sector-decomposition headlines need a quadratic form.
