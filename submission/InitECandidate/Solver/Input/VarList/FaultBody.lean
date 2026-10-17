import InitECandidate.Solver.Input.VarList.ValidBody

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

def failedIteration (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input) (index : Nat) :=
  restore source "o" (emptyLocalsHOLFinite {bind source "o" (currentWord input plan.start index) with clock:=source.clock-1})

/-- Real dynamic read and invalid-record guard, including SszErr23 and lexical
restoration. No record write or increment runs; one failure-call clock is paid. -/
theorem fault_body (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (small : index<plan.count) (previous first total : BitVec 64)
    (heap : Blob.HeapInput source input plan.inputPointer)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (p : source.locals.lookup (ofString "p")=some (.val (.word (plan.inputPointer+BitVec.ofNat 64 plan.start))))
    (previousLocal : source.locals.lookup (ofString "prev")=some (.val (.word previous)))
    (f : source.locals.lookup (ofString "first")=some (.val (.word first)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (bad : badRecord (currentWord input plan.start index) first total previous)
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source loopBody=
      (some (.exception (ofString "SszErr") (.val (.word 23#64))),failedIteration source input plan index) ∧
    emptyLocalsHOLFinite (failedIteration source input plan index)=emptyLocalsHOLFinite {source with clock:=source.clock-1} ∧
    Blob.HeapInput (failedIteration source input plan index) input plan.inputPointer := by
  classical
  let current:=currentWord input plan.start index
  let entered:=bind source "o" current
  have read:=offset_read source input plan.inputPointer plan.start index heap (plan.offset_inside index small) p i
  have eprev : entered.locals.lookup (ofString "prev")=some (.val (.word previous)) := (bind_lookup_other source "o" "prev" current (by decide)).trans previousLocal
  have ef : entered.locals.lookup (ofString "first")=some (.val (.word first)) := (bind_lookup_other source "o" "first" current (by decide)).trans f
  have en : entered.locals.lookup (ofString "len")=some (.val (.word total)) := (bind_lookup_other source "o" "len" current (by decide)).trans n
  have guarded:=record_guard entered current first total previous (bind_lookup_same _ _ _) ef en eprev failCode exceptionShape enough
  have rejected : evaluateHOLFiniteState entered recordGuard=
      (some (.exception (ofString "SszErr") (.val (.word 23#64))),emptyLocalsHOLFinite {entered with clock:=entered.clock-1}) :=
    guarded.trans (if_pos (show badRecord current first total previous from bad))
  have stopped : evaluateHOLFiniteState entered step=
      (some (.exception (ofString "SszErr") (.val (.word 23#64))),emptyLocalsHOLFinite {entered with clock:=source.clock-1}) := by
    rw [step,WitnessRadix.StateSteps.stopped_sequence entered _ recordGuard _ _ rejected (by change source.clock-1≤source.clock; omega)]
    rfl
  have declared:=ScalarScope.declare_execute source (emptyLocalsHOLFinite {entered with clock:=source.clock-1}) "o" offsetExpression current step
    (some (.exception (ofString "SszErr") (.val (.word 23#64)))) read stopped
  refine ⟨?_,rfl,?_⟩
  · rw [loop_body_shape]
    exact declared
  · exact Blob.HeapInput.of_fields source (failedIteration source input plan index) input plan.inputPointer rfl rfl rfl heap

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.fault_body
