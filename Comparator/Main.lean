/-
Comparator — statement-match + axiom-allowlist checker (Stage 5).

For each frozen claim `Realization.<name>` in Challenge.lean, checks:
1. STATEMENT: `Realization.Solution.<name>` exists and its type is
   structurally identical (up to universe-parameter renaming) to the
   frozen type — proofs may differ, statements may not.
2. AXIOMS: the solution's transitive axiom set is inside the allowlist
   {propext, Classical.choice, Quot.sound}. A dependence on `sorryAx`
   marks the theorem OPEN (not kernel-accepted at this pass).

Exit code 1 iff any MISMATCH or ILLEGAL-AXIOM is found. MISSING and OPEN
are reported truthfully (they block the done-criterion, not the build).
-/
import Lean

open Lean

def frozenNames : List Name :=
  [`kronecker_realizability, `growth_test_correct, `kalman_uniqueness,
   `unobservable_no_transfer, `graduation_frees_rank,
   `schur_flag_gaming, `no_cost_floor,
   `skew_quadratic_null, `skew_symmetric_trace_zero,
   `transfer_defect_first_order, `tilt_displaces_uniquely,
   `sym_skew_unique_decomposition, `symmetric_loop_work_zero,
   `selfSizer_exists]

def allowedAxioms : List Name :=
  [`propext, `Classical.choice, `Quot.sound]

/-- Transitive axiom dependencies of a constant. -/
partial def axiomsOf (env : Environment) (root : Name) : Array Name :=
  let rec go (n : Name) (st : NameSet × Array Name) : NameSet × Array Name :=
    if st.1.contains n then st
    else
      let st := (st.1.insert n, st.2)
      match env.find? n with
      | none => st
      | some ci =>
          let st := match ci with
            | .axiomInfo _ => (st.1, st.2.push n)
            | _ => st
          let deps := ci.type.getUsedConstants ++
            (match ci.value? with
             | some v => v.getUsedConstants
             | none => #[])
          deps.foldl (fun st d => go d st) st
  (go root ({}, #[])).2

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Realization}] {} (trustLevel := 0)
  let mut mismatches := 0
  let mut illegal := 0
  let mut missing := 0
  let mut openCnt := 0
  let mut proved := 0
  IO.println "comparator: frozen-v1 statement-match + axiom audit"
  IO.println (String.ofList (List.replicate 72 '─'))
  for n in frozenNames do
    let chName := `Realization ++ n
    let solName := `Realization ++ `Solution ++ n
    match env.find? chName, env.find? solName with
    | none, _ =>
        IO.println s!"✖ {n}: FROZEN STATEMENT MISSING from Challenge"
        mismatches := mismatches + 1
    | some _, none =>
        IO.println s!"∅ {n}: MISSING (no Solution restatement — see REGISTRY \
          for STATEMENT-DEFECT / OPEN-AT-THIS-PASS verdict)"
        missing := missing + 1
    | some ch, some sol =>
        if ch.levelParams.length != sol.levelParams.length then
          IO.println s!"✖ {n}: MISMATCH (universe arity)"
          mismatches := mismatches + 1
        else
          let solT := sol.type.instantiateLevelParams sol.levelParams
            (ch.levelParams.map Level.param)
          if ch.type != solT then
            IO.println s!"✖ {n}: MISMATCH (statement differs from frozen)"
            mismatches := mismatches + 1
          else
            let axs := axiomsOf env solName
            let sorried := axs.contains `sorryAx
            let bad := axs.filter (fun a =>
              !allowedAxioms.contains a && a != `sorryAx)
            if sorried then
              IO.println s!"◌ {n}: statement MATCH, but proof depends on \
                sorryAx — OPEN at this pass"
              openCnt := openCnt + 1
            else if !bad.isEmpty then
              IO.println s!"✖ {n}: statement MATCH, ILLEGAL AXIOMS {bad}"
              illegal := illegal + 1
            else
              IO.println s!"✔ {n}: statement MATCH, axioms {axs.toList}"
              proved := proved + 1
  IO.println (String.ofList (List.replicate 72 '─'))
  IO.println s!"proved+matched: {proved}  open: {openCnt}  missing: {missing}  \
    mismatched: {mismatches}  illegal-axioms: {illegal}"
  if mismatches + illegal > 0 then
    IO.println "comparator: RED (mismatch or illegal axiom)"
    return 1
  else
    IO.println "comparator: GREEN (no statement drift, no illegal axioms)"
    return 0
