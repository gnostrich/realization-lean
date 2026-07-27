# UNIFIED THEORY — the machine in pure mathematics
2026-07-27. Companion to THE-OBJECT.md (engineering anchor). This file is the
theory anchor: every design decision must trace to a line here or be suspect.

Setting: finite-dimensional throughout. B = the type algebra (interface/ports),
**given, not discovered** (design decision 2026-07-27: frame is an input).
E_B = conditional expectation onto B. All tags: [proven] = classical theorem,
[formal] = follows from definitions, [conj] = the empirical bet.

---

## Axiom G (the gauge principle) — one axiom, four appearances

**Only E_B-observable behavior is real. Internal coordinates are gauge.**
The system is defined up to similarity transformations acting trivially on B.

Its four appearances, previously treated as separate ideas:
1. Temporal: Kalman — minimal realizations of the same I/O behavior are
   unique up to similarity. [proven]
2. Spatial: EBR's invariant-interface rule — nothing downstream consumes
   coordinates, only intrinsic geometry and masses. [formal]
3. Across systems: transfer = re-realization of the B-valued behavior spec;
   never transport of internals. [proven via 1]
4. Across agents: human communication through a shared channel with no
   access to each other's internals. (The existence proof.)

Consequence: any method that transports gauge (activation-space linear maps
between members) violates G and fails structurally, not accidentally.
[This retro-derives the XFER abandonment from the axiom.]

---

## The object

A B-valued dynamical system:
- channel state s in a B-bimodule H (dim d)
- frozen members = response operators J_k : H → H (any modality; a member
  is nothing but its operator — Axiom G)
- ONE free energy F(s), strictly convex by construction
- exogenous input u(t) (clamps) — the only source of novelty
- temperature T — one scalar governing noise, sampler, and plasticity gate

Statics [proven, convex analysis]: unique equilibrium s*(u,tilts); Gibbs
measure ∝ exp(−F/T); linear tilts displace s* and cannot create basins.

---

## Decomposition I — of the DYNAMICS (Helmholtz/Hodge)

Any stationary diffusion with invariant Gibbs measure splits uniquely:

    drift = −∇F  ⊕  γ Ω s ,   Ω skew, divergence-free wrt the Gibbs measure

- Gradient sector: determines WHERE the system rests. Every objective,
  every tilt, every self-assessment lives here. [proven]
- Circulation sector: preserves the invariant measure exactly; determines
  ROUTES and currents; carries zero authority over preferences. [proven]

**Theorem-form of the verdict principle** [formal, from the split]:
any meter expressible as a functional of F is inside the gradient sector
and hence gameable by whatever optimizes F. The circulation sector is
provably outside every scalar objective (curl is not grad). Therefore
verdicts/vetoes MUST be circulation-sector quantities (holonomy, loop
residues) — not by discipline, by decomposition. Slide-side/loop-side
= the two Hodge sectors. The free-lunch principle is the observation
that optimization pressure lands entirely in sector one.

---

## Decomposition II — of the MEMORY KERNEL (spectral, by pole modulus)

The sequence of settled equilibria under inputs is a B-valued process.
Mori–Zwanzig with projection E_B: influence of the past enters through the
B-valued resolvent G_B(z). Kronecker/MSY [proven]:

    finite Hankel rank ⟺ rational G_B ⟺ atomic spectral measure

Decompose the kernel by pole location λ:

    |λ| ≈ 0 (transient)   =  ACTIVATIONS  (evaporates within the pass)
    0 < |λ| < 1 (interior) =  MEMORY      (the modes of m; live, updating)
    |λ| → 1 (boundary)     =  WEIGHTS     (a boundary pole with frozen
                                           residue is a CONSTANT; constants
                                           belong in the reference measure)

**The three storage media are the three regions of one spectrum.** [formal]
The fast/slow/plastic ladder is not an architecture choice; it is the
spectral decomposition of influence. Graduation = a pole reaching the
boundary with stationary residue. Growth = a new atom above the floor.

---

## The ONE certificate

Every structural event in the whole machine fires off a single test:

    a certified spectral atom above a measured noise floor

applied to different Hankel matrices:
- temporal Hankel (over time)      → memory rank growth        (shell)
- spatial Hankel (over channels)   → anchor count              (EBR)
- pole-at-boundary + frozen residue → graduation into weights  (skin)

with the veto on the irreversible event (graduation) held by a
Decomposition-I circulation quantity (holonomy vs foil floor) — the only
sector that cannot be gamed by the objective. [formal]

The noise floor is itself measured (null round-trip), not assumed.

---

## Transfer (now a theorem block, not a test program)

- T1 [proven, Kalman]: same B-valued I/O behavior ⇒ realizations unique up
  to gauge. Content is the behavior class.
- T2 [proven, Kalman decomposition]: unobservable/unreachable content
  cannot cross ANY channel-mediated protocol. Hard limit on "teaching."
- T3 [proven, Kronecker]: a behavior spec is realizable iff capacity ≥ its
  McMillan degree ⇒ transfer cost = McMillan degree, substrate-independent.
- Composition: re-realization is native in the target's algebra; the
  Hochschild first-order defect was an artifact of transporting gauge
  (violating Axiom G). On-spec composition is exact by construction.
  [formal] Only residue: off-spec generalization (empirical, deferred).

---

## Multi-member (EBR proper) [formal, from the same object at K>1]

At K ≥ 2 the coupling spectrum decomposes: agreement (common component) ⊕
coherent disagreement ⊕ incoherent residue. Memory's sharpened job: learn
the agreement subspace over time; NEVER consolidate the incoherent part
(the veto enforces this — incoherent residue fails loop closure).
Anchor count = spatial McMillan degree: the same certificate, other axis.

---

## What is proven vs what is bet

[proven/classical]: Axiom-G appearances 1–3; both decompositions; Kronecker/
MSY/Ho–Kalman; T1–T3; convex statics; skew-invariance of the Gibbs measure.

[formal/identity]: three-media-as-spectrum; verdict-principle-as-Hodge;
one-certificate-governs-all; EBR/shell as spatial/temporal cross-sections
of this object.

[conj — the ONLY empirical content]:
  C-H1: real usage produces kernels that are LOW-DEGREE ATOMIC —
        rank flat in volume, growing in diversity (both axes).
  C-OS: re-realized behaviors generalize off-spec.
Everything else is mathematics. If C-H1 fails, the machine is correct
and useless; no theorem is harmed, the bet is lost.

[proven-negative, standing guard]: no rank–cost floor; no transfer-cost
floor (HH² can vanish; Schur-flag witness). Any statement shaped like a
conservation law for antisymmetric content is quarantined.

---

## Lean mapping (implementation-faithfulness program)

C2 (the spine, one library): Kronecker, Ho–Kalman uniqueness, growth-test-
returns-true-rank, graduation-preserves-minimality, T1–T3. Exact arithmetic;
thresholded/noisy versions explicitly NOT claimed.
C3 (regression lock): Schur-flag witness as a formalized counterexample —
makes the quarantine mechanically un-reopenable.
C1 (calibration, demoted): defect identity kept as the formal autopsy of
the abandoned gauge-transport route.
Tools: Lean 4 + Mathlib + Aristotle. Cubical/rzk: no (set-level algebra;
HoTT buys nothing here). Protocol: Challenge.lean + STATEMENTS.md with
what-we-do-NOT-claim + comparator + CI (standing rule).
