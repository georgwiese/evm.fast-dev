import InitECandidate.Solver.Input.QuietClock

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Read-only finite decisions may return or raise early, but cannot write
locals/memory, spend source clocks or escape with loop break/continue. -/
inductive PureDecision : ProgHOL 64→Prop where
  | skip : PureDecision .skip
  | returned (expression : ExpHOL 64) : PureDecision (.return expression)
  | raised (name : MlS) (expression : ExpHOL 64) : PureDecision (.raise name expression)
  | ite (test : ExpHOL 64) {yes no : ProgHOL 64} (left : PureDecision yes) (right : PureDecision no) : PureDecision (.ite test yes no)
  | seq {first second : ProgHOL 64} (front : PureDecision first) (back : PureDecision second) : PureDecision (.seq first second)

theorem PureDecision.summary {F : Type} {program : ProgHOL 64} (decision : PureDecision program)
    (source : PanSemStateFiniteExact 64 F) :
    ((evaluateHOLFiniteState source program).1=none → (evaluateHOLFiniteState source program).2=source) ∧
      (evaluateHOLFiniteState source program).1≠some .break ∧ (evaluateHOLFiniteState source program).1≠some .continue := by
  classical
  induction decision generalizing source with
  | skip=>simp [evaluateHOLFiniteState_skip]
  | returned expression=>
    rw [evaluateHOLFiniteState_return]
    split <;> simp_all
    all_goals split <;> simp_all
  | raised name expression=>
    rw [evaluateHOLFiniteState_raise]
    split <;> simp_all
    all_goals split <;> simp_all
  | ite test left right leftIH rightIH=>
    rw [evaluateHOLFiniteState_ite]
    generalize read : @evalHOLExact 64 F _ source.toExact (fun address=>Classical.propDecidable (source.memaddrs address)) test=observed
    cases observed with
    | none=>simp
    | some value=>
      cases value with
      | rStruct fields=>simp
      | nStruct name fields=>simp
      | val payload=>
        cases payload with
        | word word=>
          by_cases zero : word=0
          · simpa only [if_pos zero] using rightIH source
          · simpa only [if_neg zero] using leftIH source
  | seq front back frontIH backIH=>
    rw [evaluateHOLFiniteState_seq_line780]
    have info:=frontIH source
    generalize computed : evaluateHOLFiniteState source _=output at info ⊢
    obtain ⟨result,middle⟩ := output
    cases result with
    | none=>
      have same : middle=source := info.1 rfl
      subst middle
      exact backIH source
    | some result=>exact ⟨by simp,info.2⟩

theorem PureDecision.quiet {program : ProgHOL 64} (decision : PureDecision program) (code) : QuietClock.Preserves code program := by
  induction decision with
  | skip=>exact QuietClock.skip code
  | returned expression=>exact QuietClock.returned code expression
  | raised name expression=>exact QuietClock.raised code name expression
  | ite test left right leftIH rightIH=>exact QuietClock.conditional code test _ _ leftIH rightIH
  | seq front back frontIH backIH=>exact QuietClock.sequence code _ _ frontIH backIH

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.PureDecision.summary
#print axioms InitECandidate.Solver.Input.PureDecision.quiet
