import InitECandidate.Solver.Input.PureGuard

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Prefixes with no caller return and no assignment to the tracked local.
Callees are unrestricted: scoped returns reinstall the saved caller locals. -/
inductive LocalPrefix (key : MlS) : ProgHOL 64 → Prop where
  | skip : LocalPrefix key .skip
  | assign (name : MlS) (expression : ExpHOL 64) (other : key ≠ name) :
      LocalPrefix key (.assign .local name expression)
  | seq {left right : ProgHOL 64} (first : LocalPrefix key left) (second : LocalPrefix key right) :
      LocalPrefix key (.seq left right)
  | ite (test : ExpHOL 64) {left right : ProgHOL 64}
      (first : LocalPrefix key left) (second : LocalPrefix key right) : LocalPrefix key (.ite test left right)
  | decCall (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
      {rest : ProgHOL 64} (other : key ≠ name) (tail : LocalPrefix key rest) :
      LocalPrefix key (.decCall name shape function arguments rest)

private theorem lookup_set_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (key name : MlS) (value : ValueHOL 64) (other : key ≠ name) :
    (setVarHOLFinite name value state).locals.lookup key = state.locals.lookup key := by
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, other, Ne.symm other]

private theorem lookup_restore_other (map : HolFiniteMapExact MlS (ValueHOL 64))
    (key name : MlS) (value : Option (ValueHOL 64)) (other : key ≠ name) :
    (HolFiniteMapExact.resVarEq map (name, value)).lookup key = map.lookup key := by
  rw [lookup_resVarEq_toExact]
  cases value <;> simp [resVarHOLExact, FUPDATE, FDOMSUB, other]

/-- On normal continuation the tracked binding is preserved. No program in
this class can return its caller's value, even when a helper fails. -/
theorem LocalPrefix.summary {F : Type} {key : MlS} {program : ProgHOL 64}
    (safe : LocalPrefix key program) (source : PanSemStateFiniteExact 64 F) :
    ((evaluateHOLFiniteState source program).1 = none →
      (evaluateHOLFiniteState source program).2.locals.lookup key = source.locals.lookup key) ∧
      ∀ value, (evaluateHOLFiniteState source program).1 ≠ some (.returned value) := by
  classical
  induction safe generalizing source with
  | skip => simp [evaluateHOLFiniteState_skip]
  | assign name expression other =>
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split
      · simpa only [setKvarHOLFinite] using
          And.intro (fun _ => lookup_set_other source key name _ other) (by simp)
      · simp
  | seq first second firstIH secondIH =>
    rw [evaluateHOLFiniteState_seq_line780]
    have info := firstIH source
    generalize computed : evaluateHOLFiniteState source _ = output at info ⊢
    obtain ⟨result, middle⟩ := output
    cases result with
    | none =>
      have frame := info.1 rfl
      have next := secondIH middle
      exact ⟨fun normal => (next.1 normal).trans frame, next.2⟩
    | some result => exact ⟨by simp, info.2⟩
  | ite test first second firstIH secondIH =>
    rw [evaluateHOLFiniteState_ite]
    generalize read : @evalHOLExact 64 F _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) test = observed
    cases observed with
    | none => simp
    | some value =>
      cases value with
      | val payload =>
        cases payload with
        | word word =>
          by_cases zero : word = 0
          · simpa only [if_pos zero] using secondIH source
          · simpa only [if_neg zero] using firstIH source
      | rStruct fields => simp
      | nStruct name fields => simp
  | decCall name shape function arguments other tail tailIH =>
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    split
    · simp
    · split
      · simp
      · split
        · simp
        · rename_i values args body callee returnShape called clock
          generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output
          obtain ⟨result, target⟩ := output
          simp only [computed]
          cases result with
          | none => simp
          | some result =>
            cases result with
            | returned returned =>
              simp only
              split
              · let ready := setVarHOLFinite name returned { target with locals := source.locals }
                have info := tailIH ready
                constructor
                · intro normal
                  have inner := info.1 normal
                  exact (lookup_restore_other _ key name _ other).trans
                    (inner.trans (lookup_set_other _ key name returned other))
                · exact info.2
              · simp
            | error => simp
            | timeOut => simp
            | «break» => simp
            | «continue» => simp
            | exception identifier payload => simp
            | finalFfi event => simp

/-- Expose the actual continuation state after a normal prefix. -/
theorem LocalPrefix.normal_continue {F : Type} {key : MlS} {program : ProgHOL 64}
    (safe : LocalPrefix key program) (source post : PanSemStateFiniteExact 64 F)
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.seq program continuation) = (some (.returned value), post)) :
    ∃ middle, evaluateHOLFiniteState source program = (none, middle) ∧
      evaluateHOLFiniteState middle continuation = (some (.returned value), post) ∧
      middle.locals.lookup key = source.locals.lookup key := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  have info := safe.summary source
  generalize computed : evaluateHOLFiniteState source program = output at info run
  obtain ⟨result, middle⟩ := output
  cases result with
  | none => exact ⟨middle, rfl, run, info.1 rfl⟩
  | some result => exact False.elim (info.2 value (congrArg Prod.fst run))

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.LocalPrefix.summary
#print axioms InitECandidate.Solver.Input.LocalPrefix.normal_continue
