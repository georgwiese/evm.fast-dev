import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Local preservation on continuation, allowing real early returns.
Scoped callees remain unrestricted and reinstall the actual caller locals. -/
inductive LocalFlow (key : MlS) : ProgHOL 64 → Prop where
  | base {program} (safe : LocalPrefix key program) : LocalFlow key program
  | returned (expression : ExpHOL 64) : LocalFlow key (.return expression)
  | seq {first second} (left : LocalFlow key first) (right : LocalFlow key second) : LocalFlow key (.seq first second)
  | ite (test : ExpHOL 64) {yes no} (left : LocalFlow key yes) (right : LocalFlow key no) : LocalFlow key (.ite test yes no)
  | dec (name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) {body}
      (other : key ≠ name) (tail : LocalFlow key body) : LocalFlow key (.dec name shape expression body)
  | loop (test : ExpHOL 64) {body} (safe : LocalFlow key body) : LocalFlow key (.while test body)
  | decCall (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) {body}
      (other : key ≠ name) (tail : LocalFlow key body) : LocalFlow key (.decCall name shape function arguments body)

def FlowSummary {F : Type} (key : MlS) (program : ProgHOL 64) (source : PanSemStateFiniteExact 64 F) : Prop :=
  ((evaluateHOLFiniteState source program).1 = none →
    (evaluateHOLFiniteState source program).2.locals.lookup key = source.locals.lookup key) ∧
  (evaluateHOLFiniteState source program).1 ≠ some .break ∧
  (evaluateHOLFiniteState source program).1 ≠ some .continue

/-- Actual while evaluation preserves a tracked local on fallthrough even
when a body may return from its enclosing function. -/
theorem while_flow_summary {F : Type} (key : MlS) (condition : ExpHOL 64) (body : ProgHOL 64)
    (bodySummary : ∀ source : PanSemStateFiniteExact 64 F, FlowSummary key body source)
    (source : PanSemStateFiniteExact 64 F) : FlowSummary key (.while condition body) source := by
  classical
  generalize rankEq : source.clock = rank
  induction rank using Nat.strongRecOn generalizing source with
  | ind rank ih =>
    unfold FlowSummary
    rw [evaluateHOLFiniteState_while_total]
    cases read : @evalHOLFinite 64 F _ source (fun address => Classical.propDecidable (source.memaddrs address)) condition with
    | none => simp
    | some value =>
      cases value with
      | rStruct fields => simp
      | nStruct name fields => simp
      | val payload =>
        cases payload with
        | word word =>
          simp only
          by_cases active : word ≠ 0
          · rw [if_pos active]
            by_cases zero : source.clock = 0
            · simp [zero]
            · rw [if_neg zero]
              let entry := decClockHOLFinite source
              have info := bodySummary entry
              unfold FlowSummary at info
              have clock := evaluateHOLFiniteState_clock_le entry body
              generalize bodyRun : evaluateHOLFiniteState entry body = output at info clock ⊢
              obtain ⟨result, next⟩ := output
              have nextClock : next.clock ≤ entry.clock := clock
              rw [WitnessRadix.StateSteps.fixed_clock entry next result nextClock]
              cases result with
              | none =>
                have smaller : next.clock < rank := by
                  change next.clock ≤ source.clock - 1 at nextClock
                  omega
                have tail := ih next.clock smaller next rfl
                exact ⟨fun normal => (tail.1 normal).trans (info.1 rfl), tail.2⟩
              | some result =>
                cases result with
                | «break» => exact False.elim (info.2.1 rfl)
                | «continue» => exact False.elim (info.2.2 rfl)
                | returned value => simp
                | error => simp
                | timeOut => simp
                | exception identifier payload => simp
                | finalFfi event => simp
          · rw [if_neg active]
            simp

private theorem set_other {F : Type} (source : PanSemStateFiniteExact 64 F) (key name : MlS)
    (value : ValueHOL 64) (other : key ≠ name) :
    (setVarHOLFinite name value source).locals.lookup key = source.locals.lookup key := by
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, other, Ne.symm other]

private theorem restore_other (map : HolFiniteMapExact MlS (ValueHOL 64)) (key name : MlS)
    (value : Option (ValueHOL 64)) (other : key ≠ name) :
    (HolFiniteMapExact.resVarEq map (name, value)).lookup key = map.lookup key := by
  rw [lookup_resVarEq_toExact]
  cases value <;> simp [resVarHOLExact, FUPDATE, FDOMSUB, other]

theorem LocalFlow.summary {F : Type} {key : MlS} {program : ProgHOL 64}
    (safe : LocalFlow key program) (source : PanSemStateFiniteExact 64 F) : FlowSummary key program source := by
  classical
  unfold FlowSummary
  induction safe generalizing source with
  | base safe =>
    have summary := safe.summary_full source
    exact ⟨summary.1, summary.2.2⟩
  | returned expression =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | seq left right leftIH rightIH =>
    rw [evaluateHOLFiniteState_seq_line780]
    have info := leftIH source
    generalize computed : evaluateHOLFiniteState source _ = output at info ⊢
    obtain ⟨result, middle⟩ := output
    cases result with
    | none =>
      have frame := info.1 rfl
      have next := rightIH middle
      exact ⟨fun normal => (next.1 normal).trans frame, next.2⟩
    | some result => exact ⟨by simp, info.2⟩
  | ite test left right leftIH rightIH =>
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
          · simpa only [if_pos zero] using rightIH source
          · simpa only [if_neg zero] using leftIH source
      | rStruct fields => simp
      | nStruct name fields => simp
  | dec name shape expression other tail tailIH =>
    rw [evaluateHOLFiniteState_dec_total]
    simp only
    split
    · simp
    · split
      · rename_i value read valid
        let declared := setVarHOLFinite name value source
        have info := tailIH declared
        constructor
        · intro normal
          exact (restore_other _ key name _ other).trans
            ((info.1 normal).trans (set_other source key name value other))
        · exact info.2
      · simp
  | loop test safe ih =>
    exact while_flow_summary key test _ ih source
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
              · let ready := setVarHOLFinite name returned {target with locals := source.locals}
                have info := tailIH ready
                constructor
                · intro normal
                  exact (restore_other _ key name _ other).trans
                    ((info.1 normal).trans (set_other _ key name returned other))
                · exact info.2
              · simp
            | error => simp
            | timeOut => simp
            | «break» => simp
            | «continue» => simp
            | exception identifier payload => simp
            | finalFfi event => simp

theorem LocalFlow.none_preserves {F : Type} {key : MlS} {program : ProgHOL 64}
    (safe : LocalFlow key program) (source post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState source program = (none, post)) : post.locals.lookup key = source.locals.lookup key := by
  have summary := safe.summary source
  unfold FlowSummary at summary
  rw [run] at summary
  exact summary.1 rfl

theorem LocalFlow.no_continue {F : Type} {key : MlS} {program : ProgHOL 64}
    (safe : LocalFlow key program) (source : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState source program).1 ≠ some .continue := (safe.summary source).2.2

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.LocalFlow.summary
#print axioms InitECandidate.Solver.Input.LocalFlow.none_preserves
#print axioms InitECandidate.Solver.Input.LocalFlow.no_continue

#print axioms InitECandidate.Solver.Input.while_flow_summary
