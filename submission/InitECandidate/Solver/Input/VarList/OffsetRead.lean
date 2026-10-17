import InitECandidate.Solver.Input.VarList.StepProgram

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem stride_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source offsetStride=some (.val (.word (BitVec.ofNat 64 (4*index)))) := by
  classical
  simp [eval,offsetStride,localVar,evalHOLExact,evalListHOLExact,toExact,i,valueIsWord,valueWord,panOpHOL,←BitVec.ofNat_mul,Nat.mul_comm]

/-- Actual dynamic flattened LD_LE32 in the record loop. Its four addresses
are justified by the copied slice, including arbitrary mathematical starts. -/
theorem offset_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer : BitVec 64) (start index : Nat) (heap : Blob.HeapInput source input pointer)
    (inside : start+4*index+4≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source offsetExpression=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input (start+4*index))))) := by
  have base : eval source (localVar "p")=some (.val (.word (pointer+BitVec.ofNat 64 start))) :=
    Request.local_word source "p" _ p
  exact Scalar.paired_heap_le32 source input pointer (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 (4*index))
    (localVar "p") offsetStride (start+4*index) heap inside base (stride_read source index i)
    (by simp [BitVec.ofNat_add,BitVec.add_assoc])

theorem row_address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64) (index : Nat)
    (a : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source rowPointerAddress=some (.val (.word (array+BitVec.ofNat 64 (16*index)))) := by
  classical
  simp [eval,rowPointerAddress,localVar,evalHOLExact,evalListHOLExact,toExact,a,i,valueIsWord,valueWord,
    panOpHOL,wordOpHOL,wordOp,←BitVec.ofNat_mul,Nat.mul_comm]

theorem prior_address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64) (index : Nat) (positive : 0<index)
    (a : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source priorLengthAddress=some (.val (.word (array+BitVec.ofNat 64 (16*(index-1))+8#64))) := by
  classical
  have subtract : BitVec.ofNat 64 index-1#64=BitVec.ofNat 64 (index-1) :=
    BitVec.ofNat_sub_ofNat_of_le index 1 (by decide) positive
  simp [eval,priorLengthAddress,localVar,evalHOLExact,evalListHOLExact,toExact,a,i,valueIsWord,valueWord,
    panOpHOL,wordOpHOL,wordOp,subtract,←BitVec.ofNat_mul,Nat.mul_comm,BitVec.add_assoc]

theorem pointer_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer offset : BitVec 64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (o : source.locals.lookup (ofString "o")=some (.val (.word offset))) :
    eval source rowPointerExpression=some (.val (.word (pointer+offset))) := by
  classical
  simp [eval,rowPointerExpression,localVar,evalHOLExact,evalListHOLExact,toExact,p,o,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem length_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (offset previous : BitVec 64)
    (o : source.locals.lookup (ofString "o")=some (.val (.word offset)))
    (p : source.locals.lookup (ofString "prev")=some (.val (.word previous))) :
    eval source priorLengthExpression=some (.val (.word (offset-previous))) := by
  classical
  simp [eval,priorLengthExpression,localVar,evalHOLExact,evalListHOLExact,toExact,p,o,valueIsWord,valueWord,wordOpHOL,wordOp]

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.stride_read
#print axioms InitECandidate.Solver.Input.VarList.offset_read
#print axioms InitECandidate.Solver.Input.VarList.row_address_read
#print axioms InitECandidate.Solver.Input.VarList.prior_address_read
#print axioms InitECandidate.Solver.Input.VarList.pointer_read
#print axioms InitECandidate.Solver.Input.VarList.length_read
