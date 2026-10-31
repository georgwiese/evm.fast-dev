import InitECandidate.Solver.Input.CurrentVerify.StateInitCost

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual normal state initializer return, retaining its concrete
entry/caller relation for subsequent physical-frame proofs. -/
def StateInitReturned (input : Guest.InputBlob) (caller target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si : BitVec 64) (boundary : Nat) : Prop :=
  ∃ entry value,StateInitInputs input entry pointer si boundary ∧ LocalEffects.erase entry=LocalEffects.erase caller ∧
    evaluateHOLFiniteState entry Mpt.StateInit.body=(some (.returned value),target) ∧ shapeEqHOL (shapeOfHOLExact value) .one=true

/-- Every actual state_init outcome either stops within the complete
caller allowance or resumes the original main suffix with saved caller locals.
No return or physical postcondition is assumed in advance. -/
theorem after_state_init_trace {input : Guest.InputBlob}
    {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (tables : HasTables input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterCodes=(outcome,post)) :
    source.clock-post.clock≤1757412483566 ∨ ∃ target,
      StateInitReturned input source target pointer si boundary ∧ target.clock≤source.clock ∧ source.clock-target.clock≤1757412483566 ∧
      evaluateHOLFiniteState {target with locals:=source.locals} afterStateInit=(outcome,post) := by
  rcases state_init_entry_trace tables outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨entry,target,childResult,inputs,frame,clock,childRun,resumes⟩:=reached
    have price:=state_init_price inputs
    rw [childRun] at price
    change entry.clock-target.clock≤1757412483565 at price
    have forward:=evaluateHOLFiniteState_clock_le entry Mpt.StateInit.body
    rw [childRun] at forward
    change target.clock≤entry.clock at forward
    have paid : source.clock-target.clock≤1757412483566:=by omega
    rcases resumes with stopped|⟨value,returned,checked,continued⟩
    · exact Or.inl (by rw [stopped]; exact paid)
    · rw [returned] at childRun
      exact Or.inr ⟨target,⟨entry,value,inputs,frame,childRun,checked⟩,by omega,paid,continued⟩

/-- The complete original header/gas/database/state-initialization prefix
has a uniform source allowance and retains the same actually continued main
execution. Detailed physical postconditions remain separately derived. -/
theorem to_after_state_init {input : Guest.InputBlob}
    {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤1760801932784 ∨ ∃ caller target inner,
      HasTables input caller pointer si record gasWord boundary ∧ StateInitReturned input caller target pointer si boundary ∧
      target.clock≤source.clock ∧ source.clock-target.clock≤1760801932784 ∧
      evaluateHOLFiniteState {target with locals:=caller.locals} afterStateInit=(outcome,inner) ∧
      post.clock=inner.clock ∧ LocalEffects.erase post=LocalEffects.erase inner := by
  rcases to_state_init data outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨caller,inner,tables,forward,prefixPrice,continued,endpoint,physical⟩:=reached
    rcases after_state_init_trace tables outcome continued with stopped|reached
    · exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨target,returned,childForward,childPrice,tail⟩:=reached
      exact Or.inr ⟨caller,target,inner,tables,returned,by omega,by omega,tail,endpoint,physical⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.after_state_init_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_after_state_init
