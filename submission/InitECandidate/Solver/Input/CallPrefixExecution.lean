import InitECandidate.Solver.Input.CallPrefix
import InitECandidate.Solver.Input.EvaluationOracle

namespace InitECandidate.Solver.Input.CallPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def project (output : Option (PanSemResultExact 64)×PanSemStateFiniteExact 64 Guest.HostMemory) := (output.1,output.2.clock)

/-- Retain the outcome, clock and every state field except lexical locals.
In particular, this observation retains memory, globals and the FFI state. -/
def observe (output : Option (PanSemResultExact 64)×PanSemStateFiniteExact 64 Guest.HostMemory) :=
  (project output, LocalEffects.erase output.2)

/-- One genuine reached lexical action, with its observed argument reads,
checked callee return or actual normal command. Caller locals remain in
scope at the next action; final scope restoration affects no clock. -/
inductive Reaches : PanSemStateFiniteExact 64 Guest.HostMemory→Action→PanSemStateFiniteExact 64 Guest.HostMemory→Prop where
  | declare (source name shape expression value)
      (read : WitnessRadix.QueryBranch.eval source expression=some value)
      (checked : shapeEqHOL shape (shapeOfHOLExact value)=true) :
      Reaches source (.declare name shape expression) (setVarHOLFinite name value source)
  | scoped (source name shape function arguments values body callee returnShape returned target)
      (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
      (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,returnShape))
      (funded : source.clock≠0)
      (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned returned),target))
      (checked : (shapeEqHOL (shapeOfHOLExact returned) shape && shapeEqHOL (shapeOfHOLExact returned) returnShape)=true) :
      Reaches source (.scoped name shape function arguments) (setVarHOLFinite name returned {target with locals:=source.locals})
  | command (source target command) (run : evaluateHOLFiniteState source command=(none,target)) :
      Reaches source (.command command) target

theorem Reaches.project {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {action : Action}
    (reached : Reaches source action target) (tail : ProgHOL 64) :
    project (evaluateHOLFiniteState source (program [action] tail))=project (evaluateHOLFiniteState target tail) := by
  cases reached with
  | declare name shape expression value read checked=>
    simp only [WitnessRadix.QueryBranch.eval] at read
    rw [program,evaluateHOLFiniteState_dec_total]
    simp only [read,if_pos checked,program]
    rfl
  | «scoped» name shape function arguments values body callee returnShape returned target args called funded run checked=>
    rw [program,evaluateHOLFiniteState_decCall_fixClockRewrite]
    simp only [args,called,if_neg funded,run,if_pos checked,program]
    rfl
  | command target command run=>
    rw [program,evaluateHOLFiniteState_seq_line780,run]
    rfl

theorem Reaches.runtime {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {action : Action}
    (reached : Reaches source action target) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.eshapes=source.eshapes ∧
      target.code=source.code ∧ target.ffi.oracle=source.ffi.oracle := by
  cases reached with
  | declare name shape expression value read checked=>exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | «scoped» name shape function arguments values body callee returnShape returned target args called funded run checked=>
    have fields:=evaluation_fields (callEntryStateHOLFinite source callee) target body (some (.returned returned)) run
    have oracle:=evaluation_oracle (callEntryStateHOLFinite source callee) target body (some (.returned returned)) run
    exact ⟨fields.1,fields.2.1,fields.2.2.1,fields.2.2.2,oracle⟩
  | command target command run=>
    have fields:=evaluation_fields source target command none run
    exact ⟨fields.1,fields.2.1,fields.2.2.1,fields.2.2.2,evaluation_oracle source target command none run⟩

/-- Lexical restoration changes only caller locals. Its actual memory,
globals and FFI state agree with the genuine reached continuation. -/
theorem Reaches.erase {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {action : Action}
    (reached : Reaches source action target) (tail : ProgHOL 64) :
    LocalEffects.erase (evaluateHOLFiniteState source (program [action] tail)).2=
      LocalEffects.erase (evaluateHOLFiniteState target tail).2 := by
  cases reached with
  | declare name shape expression value read checked=>
    simp only [WitnessRadix.QueryBranch.eval] at read
    rw [program,evaluateHOLFiniteState_dec_total]
    simp only [read,if_pos checked,program]
    rfl
  | «scoped» name shape function arguments values body callee returnShape returned target args called funded run checked=>
    rw [program,evaluateHOLFiniteState_decCall_fixClockRewrite]
    simp only [args,called,if_neg funded,run,if_pos checked,program]
    rfl
  | command target command run=>
    rw [program,evaluateHOLFiniteState_seq_line780,run]
    rfl

inductive Execution : PanSemStateFiniteExact 64 Guest.HostMemory→List Action→PanSemStateFiniteExact 64 Guest.HostMemory→Prop where
  | done (source) : Execution source [] source
  | step {source middle target action rest} (first : Reaches source action middle) (next : Execution middle rest target) :
      Execution source (action::rest) target

theorem Reaches.observe {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {action : Action}
    (reached : Reaches source action target) (tail : ProgHOL 64) :
    observe (evaluateHOLFiniteState source (program [action] tail))=
      observe (evaluateHOLFiniteState target tail) :=
  Prod.ext (reached.project tail) (reached.erase tail)

theorem program_cons (action : Action) (rest : List Action) (tail : ProgHOL 64) :
    program (action::rest) tail=program [action] (program rest tail) := by cases action <;> rfl

theorem Execution.project {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {actions : List Action}
    (execution : Execution source actions target) (tail : ProgHOL 64) :
    project (evaluateHOLFiniteState source (program actions tail))=project (evaluateHOLFiniteState target tail) := by
  induction execution with
  | done source=>rfl
  | step first next ih=>rw [program_cons]; exact (first.project _).trans ih

theorem Execution.skip_clock {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {actions : List Action}
    (execution : Execution source actions target) :
    (evaluateHOLFiniteState source (program actions .skip)).2.clock=target.clock := by
  have clocks:=congrArg Prod.snd (execution.project .skip)
  simpa only [CallPrefix.project,evaluateHOLFiniteState_skip] using clocks

theorem Execution.forward {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {actions : List Action}
    (execution : Execution source actions target) : target.clock≤source.clock := by
  have clock:=evaluateHOLFiniteState_clock_le source (program actions .skip)
  rw [execution.skip_clock] at clock
  exact clock

/-- Every reached action retains the actual memory domain, byte order,
exception declarations, original code and oracle function. -/
theorem Execution.runtime {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {actions : List Action}
    (execution : Execution source actions target) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.eshapes=source.eshapes ∧
      target.code=source.code ∧ target.ffi.oracle=source.ffi.oracle := by
  induction execution with
  | done source=>exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | step first next ih=>
    obtain ⟨domain,endian,exceptions,code,oracle⟩:=first.runtime
    obtain ⟨nextDomain,nextEndian,nextExceptions,nextCode,nextOracle⟩:=ih
    exact ⟨nextDomain.trans domain,nextEndian.trans endian,nextExceptions.trans exceptions,nextCode.trans code,nextOracle.trans oracle⟩

theorem Execution.erase {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {actions : List Action}
    (execution : Execution source actions target) (tail : ProgHOL 64) :
    LocalEffects.erase (evaluateHOLFiniteState source (program actions tail)).2=
      LocalEffects.erase (evaluateHOLFiniteState target tail).2 := by
  induction execution with
  | done source=>rfl
  | step first next ih=>rw [program_cons]; exact (first.erase _).trans ih

theorem Execution.skip_erase {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {actions : List Action}
    (execution : Execution source actions target) :
    LocalEffects.erase (evaluateHOLFiniteState source (program actions .skip)).2=LocalEffects.erase target := by
  have same:=execution.erase .skip
  simpa only [evaluateHOLFiniteState_skip] using same

theorem Execution.observe {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {actions : List Action}
    (execution : Execution source actions target) (tail : ProgHOL 64) :
    observe (evaluateHOLFiniteState source (program actions tail))=
      observe (evaluateHOLFiniteState target tail) :=
  Prod.ext (execution.project tail) (execution.erase tail)

/-- Split an observed action trace without reevaluating it or restoring
its still-live lexical bindings. -/
theorem Execution.split {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (front back : List Action) (execution : Execution source (front ++ back) target) :
    ∃ middle, Execution source front middle ∧ Execution middle back target := by
  induction front generalizing source with
  | nil => exact ⟨source, .done source, execution⟩
  | cons action rest ih =>
    cases execution with
    | step first next =>
      obtain ⟨middle, left, right⟩ := ih next
      exact ⟨middle, .step first left, right⟩

theorem Execution.singleton {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {action : Action}
    (execution : Execution source [action] target) : Reaches source action target := by
  cases execution with
  | step first next => cases next; exact first

theorem Execution.layout {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {actions : List Action}
    (execution : Execution source actions target) :
    target.shMemaddrs=source.shMemaddrs ∧ target.baseAddr=source.baseAddr := by
  have fields := evaluation_layout source (evaluateHOLFiniteState source (program actions .skip)).2
    (program actions .skip) (evaluateHOLFiniteState source (program actions .skip)).1 rfl
  have shared := congrArg PanSemStateFiniteExact.shMemaddrs execution.skip_erase
  have base := congrArg PanSemStateFiniteExact.baseAddr execution.skip_erase
  exact ⟨shared.symm.trans fields.1, base.symm.trans fields.2⟩

theorem Reaches.layout {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {action : Action}
    (reached : Reaches source action target) :
    target.shMemaddrs=source.shMemaddrs ∧ target.baseAddr=source.baseAddr :=
  (Execution.step reached (.done target)).layout

end InitECandidate.Solver.Input.CallPrefix

#print axioms InitECandidate.Solver.Input.CallPrefix.Reaches.project
#print axioms InitECandidate.Solver.Input.CallPrefix.Reaches.runtime
#print axioms InitECandidate.Solver.Input.CallPrefix.Reaches.erase
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.project
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.skip_clock
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.forward
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.runtime
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.erase
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.skip_erase
#print axioms InitECandidate.Solver.Input.CallPrefix.Reaches.observe
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.observe
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.split
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.singleton
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.layout
#print axioms InitECandidate.Solver.Input.CallPrefix.Reaches.layout
