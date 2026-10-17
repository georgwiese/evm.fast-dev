import InitECandidate.Solver.Input.VarList.Filled
import InitECandidate.Solver.Input.VarList.WalkPrevious
import InitECandidate.Solver.Input.VarList.AnyLoop

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def pairValue (array : BitVec 64) (count : Nat) : ValueHOL 64 := .rStruct [.val (.word array),.val (.word (BitVec.ofNat 64 count))]
def finished (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64) (count : Nat) (total previous : BitVec 64) :=
  {source with memory:=WitnessRadix.StoreWord.put source.memory (lengthCell array (count-1)) (total-previous)}

theorem final_address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64) (count : Nat) (positive : 0<count)
    (a : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (c : source.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 count)))) :
    eval source finalAddress=some (.val (.word (lengthCell array (count-1)))) := by
  classical
  have subtraction : BitVec.ofNat 64 count-1#64=BitVec.ofNat 64 (count-1) := BitVec.ofNat_sub_ofNat_of_le count 1 (by decide) positive
  simp [eval,finalAddress,lengthCell,row,localVar,evalHOLExact,evalListHOLExact,toExact,a,c,valueIsWord,valueWord,
    panOpHOL,wordOpHOL,wordOp,subtraction,←BitVec.ofNat_mul,Nat.mul_comm,BitVec.add_assoc]

theorem final_value_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (total previous : BitVec 64)
    (n : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (p : source.locals.lookup (ofString "prev")=some (.val (.word previous))) :
    eval source finalExpression=some (.val (.word (total-previous))) := by
  classical
  simp [eval,finalExpression,localVar,evalHOLExact,evalListHOLExact,toExact,n,p,valueIsWord,valueWord,wordOpHOL,wordOp]

/-- Actual final record-length store and pair return. Natural fresh allocation
geometry derives mapping and the copied-input frame; no body clock is paid. -/
theorem return_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (total previous : BitVec 64) (heap : Blob.HeapInput source input plan.inputPointer) (domain : source.memaddrs=InitE.ordinaryDomain)
    (a : source.locals.lookup (ofString "arr")=some (.val (.word plan.array)))
    (c : source.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 plan.count))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (p : source.locals.lookup (ofString "prev")=some (.val (.word previous))) :
    evaluateHOLFiniteState source afterLoop=
      (some (.returned (pairValue plan.array plan.count)),emptyLocalsHOLFinite (finished source plan.array plan.count total previous)) ∧
    Blob.HeapInput (emptyLocalsHOLFinite (finished source plan.array plan.count total previous)) input plan.inputPointer ∧
    WitnessRadix.BackingLayout.control (emptyLocalsHOLFinite (finished source plan.array plan.count total previous))=WitnessRadix.BackingLayout.control source ∧
    ArrayFrame source (emptyLocalsHOLFinite (finished source plan.array plan.count total previous)) input plan := by
  classical
  have address:=final_address_read source plan.array plan.count plan.positive a c
  have value:=final_value_read source total previous n p
  have stored:=WitnessRadix.StoreWord.execute source finalAddress finalExpression (lengthCell plan.array (plan.count-1)) (total-previous)
    address value (plan.length_mapped source domain (plan.count-1) (by have h:=plan.positive; omega))
  have storeRun : evaluateHOLFiniteState source finalLengthStore=(none,finished source plan.array plan.count total previous) := by
    rw [final_store_shape]
    exact stored
  let target:=finished source plan.array plan.count total previous
  have returned : evaluateHOLFiniteState target returnArray=(some (.returned (pairValue plan.array plan.count)),emptyLocalsHOLFinite target) := by
    simp [target,finished,returnArray,pairValue,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,a,c,
      shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have targetHeap : Blob.HeapInput target input plan.inputPointer :=
    plan.length_store_input source heap (plan.count-1) (by have h:=plan.positive; omega) (total-previous)
  refine ⟨?_,Blob.HeapInput.of_fields target (emptyLocalsHOLFinite target) input plan.inputPointer rfl rfl rfl targetHeap,rfl,?_⟩
  · rw [after_loop_shape,WitnessRadix.StateSteps.next_sequence source target finalLengthStore returnArray storeRun (Nat.le_refl _)]
    exact returned
  · exact store_frame source input plan (lengthCell plan.array (plan.count-1)) (total-previous)
      (plan.length_inside (plan.count-1) (by have h:=plan.positive; omega))

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.final_address_read
#print axioms InitECandidate.Solver.Input.VarList.final_value_read
#print axioms InitECandidate.Solver.Input.VarList.return_execute
