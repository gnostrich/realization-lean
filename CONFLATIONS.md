# CONFLATIONS.md — conflation check before formalization
2026-07-27. Audit of the whole session + theory docs for places where TWO
DISTINCT FORMAL OBJECTS share one name or one claimed identity. Lean forces
disambiguation eventually; doing it now is the clean starting point.
Severity: FATAL = would make the proved theorem ≠ the used/claimed one.
TERM = terminology freeze needed. Each entry: the two objects / where
conflated / the fix (applied in this commit where marked ✎).

## F1 [FATAL] "Hankel matrix" — Markov-parameter Hankel vs trajectory Hankel
(a) Behavior Hankel: blocks g(i+j) where g(k)=CA^kB — the Kronecker object,
    what Challenge.lean defines and proves about.
(b) Data/trajectory Hankel of a residual TIME SERIES (subspace-ID style) —
    what the deployed growth test §6 builds from e_t. Its rank equals system
    order only under excitation conditions (Willems' fundamental lemma
    territory), NOT by Kronecker.
Conflated in: shell spec §6, all growth-test talk this session.
Consequence: growth_test_correct as proved does NOT license the test as
implemented.
FIX ✎: implementation is REALIGNED to the theorem — the deployed test must
first estimate the kernel's Markov parameters (the RLS fit already produces
(A,B,C); form ĝ(k)=ĈÂᵏB̂ or impulse-response estimates), then Hankel THOSE.
Trajectory-Hankel shortcut is FORBIDDEN unless a Willems-type statement is
separately claimed — it is not: new non-claim 11.

## F2 [FATAL] "Atom" — spectral atom vs statistical stationarity
(a) Atom of the kernel's spectral measure = a pole of the rational function
    (structure; every pole of a rational kernel is one).
(b) "An atom has formed" = an ESTIMATED pole's parameters have stopped
    changing (statistics of an estimator).
Conflated in: all graduation talk ("atomicity as graduation certificate").
Consequence: graduation_frees_rank is about deleting a pole from an exact
kernel; the deployed gate is a stationarity test on estimates. Same
exact-vs-noisy split as non-claim 1, but the shared word "atom" is a
regression vector.
FIX ✎ terminology freeze: "pole" (formal object) / "pole-stationarity test"
(deployed gate). The word "atom" is reserved for the spectral-measure sense
ONLY (Kronecker/MSY contexts). Deployed-gate correctness stays under
non-claim 1.

## F3 [FATAL] "Holonomy" — field loop-work vs map-composition return residue
(a) Loop work of a drift FIELD around a closed polygon — what
    symmetric_loop_work_zero proves is blind to the symmetric sector.
(b) Return residue of composed nonlinear MAPS around a loop (EBR G4 meter,
    the membrane loop test) — holonomy of a connection; a different object.
(c) Lévy area / Ω accumulation — level-2 signature of a trajectory.
Conflated in: UNIFIED-THEORY's "verdict principle as theorem" sentence; my
claim that the veto's ungameability is proved.
Consequence: ungameability is PROVED only for (a). For (b) it is a design
claim whose linearized shadow is (a). Overclaim as written.
FIX ✎: terminology — "loop work" (a, proved), "return residue" (b,
measured/design), "signed area" (c, register). UNIFIED-THEORY sentence
weakened; COVERAGE row split; new non-claim 12 (map-composition meter
blindness not claimed as theorem).

## F4 [FATAL] "Strictly convex F by construction" — designed vs effective
(a) The DESIGNED quadratic part of F (clamp+anchor+coupling penalty
    weights): PosDef, statics theorem applies.
(b) The EFFECTIVE objective through the frozen member, s ↦ ½κ‖s−R(LM(W(s)))‖²:
    NOT convex in general; the bowl story rests on a frozen-member
    linearization / contraction assumption.
Conflated in: UNIFIED-THEORY "Statics [proven]" line; shell spec bowl talk.
Consequence: tilt_displaces_uniquely covers (a) only.
FIX ✎: theory wording patched to "quadratic model / linearized regime";
global well-posedness of the coupled fixed point = new non-claim 13
(a design condition: contraction of the settle map, checkable at runtime,
never a theorem here).

## F5 [FATAL-for-C-H1] "McMillan degree of the usage distribution"
(a) McMillan degree of a single deterministic behavior (classical; T3).
(b) "Degree of the task/usage distribution's resolvent" (aggregator + H1
    language) — a population/ensemble object with no classical definition.
Consequence: C-H1 is not even well-posed until (b) is defined.
FIX ✎: conjecture-side definition adopted (NOT in Challenge.lean):
empirical McMillan degree := rank of the Hankel of the population
conditional-mean kernel E[e_t | past], with identifiability conditions an
explicit part of the conjecture, not assumed. Recorded in COVERAGE as part
of [N]3.

## T6 [TERM] "G_B" — operator resolvent vs transfer function
E_B[(z−T)⁻¹] (Conjecture-1 object, fixed operator wrt subalgebra) vs
C(zI−A)⁻¹B (transfer function of an identified system). Same rational/
Hankel form; different objects; identification is exactly the Phase-2/OV
bridge and must not be used before it. Freeze: scalar docs say "transfer
function"; "resolvent" reserved for OV contexts. UNIFIED-THEORY wording ✎.

## T7 [TERM] "B" — three usages
(i) typed-port index (design), (ii) subalgebra with E_B (OV, Phase 2),
(iii) the concrete given frame P (an instance of (i)). Phase-1 claims have
B trivial; the theory header's E_B is aspirational. Freeze: Phase-1 text
says "interface types"; E_B appears only in Phase-2 sections.

## T8 [TERM] "Gauge" — GL similarity vs isometry vs signed permutation
Axiom-G formal content = GL similarity (Kalman). EBR's invariance =
isometry of intrinsic geometry. MLP symmetry = signed permutations.
Nested, not equal. Claims fix GL; others are design-level invariances.

## T9 [TERM] "Mode" vs "behavior"; finite fingerprint vs infinite sequence
A mode = degree-1 kernel component; a behavior = full I/O map; a
fingerprint = FINITE probe data. Bridge is classical partial realization
(finite data always extends; minimal extension degree = its Hankel rank) —
and growth_test_correct's two-consecutive-sizes condition is exactly that
statement, so the bridge is inside the claims. No new claim needed; freeze
the three words.

## T10 [TERM] "Certificate" — Hankel/pole tests vs CPP positivity certs
Structural rhyme only (finite certificate decides infinite family). Never
weld; already tagged; recorded here so it stays a rhyme.

## Terminology freeze (one name, one object)
| name | reserved for |
|---|---|
| Hankel (behavior) | blocks g(i+j), g = Markov params |
| trajectory Hankel | shifted-window data matrix (FORBIDDEN in claims) |
| pole | eigenvalue of A / pole of transfer function |
| atom | spectral-measure sense only (Kronecker/MSY) |
| pole-stationarity test | the deployed graduation gate |
| loop work | field integral around polygon (proved object) |
| return residue | map-composition loop measurement (G4/membrane) |
| signed area | Ω / level-2 signature |
| transfer function | C(zI−A)⁻¹B (scalar Phase 1) |
| resolvent | E_B[(z−T)⁻¹] (OV Phase 2 only) |
| interface types | Phase-1 name for B-as-design |
| empirical McMillan degree | conjecture-side population object (defined F5) |

Status after this commit: F1–F5 fixed by realignment/wording/non-claims
11–13; T6–T10 frozen. Clean start achieved iff future text obeys the
freeze table; violations are regressions by definition.
