import InitECandidate.Solver.Input.OffsetsEnvironment

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Real ignored-result validator call, including callee ABI and caller-local
restoration. Every mapped array is covered; normal resumption proves first=fixed.
The call and whole validator cost at most count+2 source clocks. -/
theorem call_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (expressions : List (ExpHOL 64))
    (pointer fixed total : BitVec 64) (offsets : Nat→BitVec 64) (count : Nat) (positive : 0<count) (small : count≤8)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=
      some (arguments pointer fixed total count))
    (code : source.code.lookup (ofString "ssz_check_offsets")=some (formals,body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (mapped : ∀ position<count,source.memaddrs (pointer+BitVec.ofNat 64 (8*position)))
    (cells : ∀ position<count,source.memory (pointer+BitVec.ofNat 64 (8*position))=.word (offsets position))
    (enough : count+2≤source.clock) :
    ∃ result target paid,
      evaluateHOLFiniteState source (.call (some (none,none)) (ofString "ssz_check_offsets") expressions)=(result,target) ∧
      paid≤count+2 ∧ emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} ∧
      ((result=none ∧ offsets 0=fixed ∧ target.locals=source.locals ∧
        ∀ position<count,ValidAt fixed total offsets position) ∨
        ∃ error : BitVec 64,(error=10#64 ∨ error=11#64 ∨ error=12#64) ∧
          result=some (.exception (ofString "SszErr") (.val (.word error)))) := by
  classical
  obtain ⟨callee,called,p,n,f,l⟩:=environment source.code.lookup pointer fixed total count code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨result,post,paid,run,bound,frame,outcome⟩:=any_execute entry pointer fixed total offsets count positive small
    p n f l mapped cells failCode exceptionShape (by change count+1≤source.clock-1; omega)
  have frameAfter : emptyLocalsHOLFinite post=emptyLocalsHOLFinite {source with clock:=source.clock-(paid+1)} := by
    rw [frame]
    change emptyLocalsHOLFinite {source with clock:=source.clock-1-paid}=_
    have clock : source.clock-1-paid=source.clock-(paid+1) := by omega
    rw [clock]
  rcases outcome with normal|fault
  · obtain ⟨rfl,first,valid⟩:=normal
    have calledRun:=evaluateHOLFiniteState_call_return_caller_locals source none (ofString "ssz_check_offsets") expressions
      (arguments pointer fixed total count) body callee .one (.val (.word 0#64)) post args called (by omega) run (by simp [shapeEqHOL,shapeOfHOLExact])
    exact ⟨none,{post with locals:=source.locals},paid+1,calledRun,by omega,frameAfter,Or.inl ⟨rfl,first,rfl,valid⟩⟩
  · obtain ⟨error,allowed,rfl⟩:=fault
    have calledRun:=evaluateHOLFiniteState_call_exception_no_handler source none (ofString "ssz_check_offsets") expressions
      (arguments pointer fixed total count) body callee .one (ofString "SszErr") (.val (.word error)) post args called (by omega) run
    exact ⟨_,emptyLocalsHOLFinite post,paid+1,calledRun,by omega,frameAfter,Or.inr ⟨error,allowed,rfl⟩⟩

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.call_execute
