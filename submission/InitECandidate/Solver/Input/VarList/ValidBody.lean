import InitECandidate.Solver.Input.VarList.ValidStep
import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

def currentWord (input : Guest.InputBlob) (start index : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (Guest.GasLimit.le32 input (start+4*index))
def iteration (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (previous : BitVec 64) :=
  restore source "o" (stepState (bind source "o" (currentWord input plan.start index)) input plan index (currentWord input plan.start index) previous)

set_option maxHeartbeats 20000

/-- Actual complete record-loop body, including the copied dynamic offset
read, local scope, all guard/store/update commands and lexical restoration. -/
theorem valid_body (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (small : index<plan.count) (previous first total : BitVec 64)
    (heap : Blob.HeapInput source input plan.inputPointer) (domain : source.memaddrs=InitE.ordinaryDomain)
    (a : source.locals.lookup (ofString "arr")=some (.val (.word plan.array)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (p : source.locals.lookup (ofString "p")=some (.val (.word (plan.inputPointer+BitVec.ofNat 64 plan.start))))
    (previousLocal : source.locals.lookup (ofString "prev")=some (.val (.word previous)))
    (f : source.locals.lookup (ofString "first")=some (.val (.word first)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (valid : ¬badRecord (currentWord input plan.start index) first total previous) :
    evaluateHOLFiniteState source loopBody=(none,iteration source input plan index previous) ∧
      Blob.HeapInput (iteration source input plan index previous) input plan.inputPointer := by
  let current:=currentWord input plan.start index
  let entered:=bind source "o" current
  have read:=offset_read source input plan.inputPointer plan.start index heap (plan.offset_inside index small) p i
  have enteredHeap : Blob.HeapInput entered input plan.inputPointer := Blob.HeapInput.bind source input plan.inputPointer "o" current heap
  have ea : entered.locals.lookup (ofString "arr")=some (.val (.word plan.array)) := (bind_lookup_other source "o" "arr" current (by decide)).trans a
  have ei : entered.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) := (bind_lookup_other source "o" "i" current (by decide)).trans i
  have ep : entered.locals.lookup (ofString "p")=some (.val (.word (plan.inputPointer+BitVec.ofNat 64 plan.start))) := (bind_lookup_other source "o" "p" current (by decide)).trans p
  have eprev : entered.locals.lookup (ofString "prev")=some (.val (.word previous)) := (bind_lookup_other source "o" "prev" current (by decide)).trans previousLocal
  have ef : entered.locals.lookup (ofString "first")=some (.val (.word first)) := (bind_lookup_other source "o" "first" current (by decide)).trans f
  have en : entered.locals.lookup (ofString "len")=some (.val (.word total)) := (bind_lookup_other source "o" "len" current (by decide)).trans n
  obtain ⟨stepRun,stepHeap⟩:=valid_step entered input plan index small current previous first total enteredHeap domain ea ei (bind_lookup_same _ _ _) ep eprev ef en valid
  have declared:=ScalarScope.declare_execute source (stepState entered input plan index current previous) "o" offsetExpression current step none read stepRun
  refine ⟨?_,?_⟩
  · rw [loop_body_shape]
    exact declared
  · exact Blob.HeapInput.restore source (stepState entered input plan index current previous) input plan.inputPointer "o" stepHeap

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.valid_body
