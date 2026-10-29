import InitECandidate.Solver.Input.CallPrefixExecution

namespace InitECandidate.Solver.Input.CallPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def Stopped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (actions : List Action) : Prop :=
  ∀ tail,project (evaluateHOLFiniteState source (program actions tail))=project (evaluateHOLFiniteState source (program actions .skip))

/-- A stopped prefix retains its actual nonlocal state as well as its
outcome and clock. Changing the unevaluated tail affects none of these. -/
def StoppedFrame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (actions : List Action) : Prop :=
  ∀ tail,observe (evaluateHOLFiniteState source (program actions tail))=
    observe (evaluateHOLFiniteState source (program actions .skip))

theorem StoppedFrame.stopped {source : PanSemStateFiniteExact 64 Guest.HostMemory} {actions : List Action}
    (stopped : StoppedFrame source actions) : Stopped source actions :=
  fun tail => congrArg Prod.fst (stopped tail)

/-- Classify one actual lexical action. Only an observed checked helper
return enters its continuation; every other helper outcome stops here. -/
theorem action_classify_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (action : Action) :
    StoppedFrame source [action] ∨ ∃ target,Reaches source action target := by
  classical
  cases action with
  | declare name shape expression=>
    cases read : WitnessRadix.QueryBranch.eval source expression with
    | none=>
      simp only [WitnessRadix.QueryBranch.eval] at read
      exact Or.inl (by intro tail; simp only [program,evaluateHOLFiniteState_dec_total,read] <;> rfl)
    | some value=>
      by_cases checked : shapeEqHOL shape (shapeOfHOLExact value)=true
      · exact Or.inr ⟨_,.declare source name shape expression value read checked⟩
      · simp only [WitnessRadix.QueryBranch.eval] at read
        exact Or.inl (by intro tail; simp only [program,evaluateHOLFiniteState_dec_total,read,if_neg checked] <;> rfl)
  | command command=>
    cases run : evaluateHOLFiniteState source command with
    | mk result target=>
      cases result with
      | none=>exact Or.inr ⟨target,.command source target command run⟩
      | some result=>exact Or.inl (by intro tail; simp only [program,evaluateHOLFiniteState_seq_line780,run] <;> rfl)
  | «scoped» name shape function arguments=>
    cases args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments with
    | none=>exact Or.inl (by intro tail; simp only [program,evaluateHOLFiniteState_decCall_fixClockRewrite,args] <;> rfl)
    | some values=>
      cases called : lookupCodeHOLFinite source.code.lookup function values with
      | none=>exact Or.inl (by intro tail; simp only [program,evaluateHOLFiniteState_decCall_fixClockRewrite,args,called] <;> rfl)
      | some data=>
        obtain ⟨body,callee,returnShape⟩:=data
        by_cases zero : source.clock=0
        · exact Or.inl (by intro tail; simp only [program,evaluateHOLFiniteState_decCall_fixClockRewrite,args,called,if_pos zero] <;> rfl)
        · generalize run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output
          obtain ⟨result,target⟩:=output
          cases result with
          | none=>exact Or.inl (by intro tail; simp only [program,evaluateHOLFiniteState_decCall_fixClockRewrite,args,called,if_neg zero,run] <;> rfl)
          | some result=>
            cases result with
            | returned returned=>
              by_cases checked : (shapeEqHOL (shapeOfHOLExact returned) shape && shapeEqHOL (shapeOfHOLExact returned) returnShape)=true
              · exact Or.inr ⟨_,.scoped source name shape function arguments values body callee returnShape returned target args called zero run checked⟩
              · exact Or.inl (by intro tail; simp only [program,evaluateHOLFiniteState_decCall_fixClockRewrite,args,called,if_neg zero,run,if_neg checked] <;> rfl)
            | _=>exact Or.inl (by intro tail; simp only [program,evaluateHOLFiniteState_decCall_fixClockRewrite,args,called,if_neg zero,run] <;> rfl)

theorem classify_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (actions : List Action) :
    StoppedFrame source actions ∨ ∃ target,Execution source actions target := by
  induction actions generalizing source with
  | nil=>exact Or.inr ⟨source,.done source⟩
  | cons action rest ih=>
    rcases action_classify_frame source action with stopped|reached
    · exact Or.inl (by intro tail; rw [program_cons action rest tail,program_cons action rest .skip]; exact (stopped _).trans (stopped _).symm)
    · obtain ⟨middle,first⟩:=reached
      rcases ih middle with stopped|reached
      · exact Or.inl (by intro tail; rw [program_cons action rest tail,program_cons action rest .skip]; exact (first.observe _).trans ((stopped tail).trans (first.observe _).symm))
      · obtain ⟨target,next⟩:=reached
        exact Or.inr ⟨target,.step first next⟩

/-- Compatibility projection for callers which only need clocks and outcomes. -/
theorem action_classify (source : PanSemStateFiniteExact 64 Guest.HostMemory) (action : Action) :
    Stopped source [action] ∨ ∃ target,Reaches source action target :=
  (action_classify_frame source action).imp StoppedFrame.stopped id

theorem classify (source : PanSemStateFiniteExact 64 Guest.HostMemory) (actions : List Action) :
    Stopped source actions ∨ ∃ target,Execution source actions target :=
  (classify_frame source actions).imp StoppedFrame.stopped id

/-- A prefix priced with a skip sink either stops within that allowance or
exposes the actual reached continuation and a concrete action trace. Scope
restorations retain the actual outcome and final clock on every path. -/
theorem priced_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (actions : List Action) (tail : ProgHOL 64) (price : Nat)
    (priced : source.clock-(evaluateHOLFiniteState source (program actions .skip)).2.clock≤price)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (program actions tail)=(outcome,post)) :
    (source.clock-post.clock≤price ∧ outcome=(evaluateHOLFiniteState source (program actions .skip)).1) ∨ ∃ current inner,Execution source actions current ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤price ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current tail=(outcome,inner) := by
  rcases classify source actions with stopped|reached
  · have equal:=congrArg Prod.snd (stopped tail)
    rw [run] at equal
    change post.clock=(evaluateHOLFiniteState source (program actions .skip)).2.clock at equal
    have resultEq:=congrArg Prod.fst (stopped tail)
    rw [run] at resultEq
    exact Or.inl ⟨by rw [equal]; exact priced,resultEq⟩
  · obtain ⟨current,execution⟩:=reached
    have replay:=execution.project tail
    rw [run] at replay
    have resultEq:=congrArg Prod.fst replay
    have clockEq:=congrArg Prod.snd replay
    change outcome=(evaluateHOLFiniteState current tail).1 at resultEq
    change post.clock=(evaluateHOLFiniteState current tail).2.clock at clockEq
    rw [execution.skip_clock] at priced
    exact Or.inr ⟨current,(evaluateHOLFiniteState current tail).2,execution,execution.forward,priced,clockEq,Prod.ext resultEq.symm rfl⟩

end InitECandidate.Solver.Input.CallPrefix

#print axioms InitECandidate.Solver.Input.CallPrefix.action_classify
#print axioms InitECandidate.Solver.Input.CallPrefix.classify
#print axioms InitECandidate.Solver.Input.CallPrefix.priced_trace

#print axioms InitECandidate.Solver.Input.CallPrefix.action_classify_frame
#print axioms InitECandidate.Solver.Input.CallPrefix.classify_frame
#print axioms InitECandidate.Solver.Input.CallPrefix.StoppedFrame.stopped

namespace InitECandidate.Solver.Input.CallPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Lexical scope restoration changes neither the observed final clock nor
any state field other than locals. Keep this observation as one trace field. -/
structure ScopeFrame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  clock : source.clock=target.clock
  metadata : LocalEffects.erase source=LocalEffects.erase target

theorem ScopeFrame.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) : ScopeFrame source source := ⟨rfl,rfl⟩

theorem ScopeFrame.trans {source middle target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (first : ScopeFrame source middle) (second : ScopeFrame middle target) : ScopeFrame source target :=
  ⟨first.clock.trans second.clock,first.metadata.trans second.metadata⟩

/-- The priced actual prefix trace, retaining the complete scope observation
needed when its continuation later returns to an enclosing caller. -/
theorem priced_frame_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (actions : List Action) (tail : ProgHOL 64) (price : Nat)
    (priced : source.clock-(evaluateHOLFiniteState source (program actions .skip)).2.clock≤price)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (program actions tail)=(outcome,post)) :
    (source.clock-post.clock≤price ∧ outcome=(evaluateHOLFiniteState source (program actions .skip)).1) ∨
      ∃ current inner,Execution source actions current ∧ current.clock≤source.clock ∧ source.clock-current.clock≤price ∧
        ScopeFrame post inner ∧ evaluateHOLFiniteState current tail=(outcome,inner) := by
  rcases classify_frame source actions with stopped|reached
  · have plain:=stopped.stopped
    have equal:=congrArg Prod.snd (plain tail)
    rw [run] at equal
    change post.clock=(evaluateHOLFiniteState source (program actions .skip)).2.clock at equal
    have resultEq:=congrArg Prod.fst (plain tail)
    rw [run] at resultEq
    exact Or.inl ⟨by rw [equal]; exact priced,resultEq⟩
  · obtain ⟨current,execution⟩:=reached
    have replay:=execution.observe tail
    rw [run] at replay
    have resultEq:=congrArg (fun observed=>observed.1.1) replay
    have clockEq:=congrArg (fun observed=>observed.1.2) replay
    have metadata:=congrArg Prod.snd replay
    change outcome=(evaluateHOLFiniteState current tail).1 at resultEq
    change post.clock=(evaluateHOLFiniteState current tail).2.clock at clockEq
    rw [execution.skip_clock] at priced
    exact Or.inr ⟨current,(evaluateHOLFiniteState current tail).2,execution,execution.forward,priced,⟨clockEq,metadata⟩,Prod.ext resultEq.symm rfl⟩

end InitECandidate.Solver.Input.CallPrefix

#print axioms InitECandidate.Solver.Input.CallPrefix.ScopeFrame.refl
#print axioms InitECandidate.Solver.Input.CallPrefix.ScopeFrame.trans
#print axioms InitECandidate.Solver.Input.CallPrefix.priced_frame_trace
