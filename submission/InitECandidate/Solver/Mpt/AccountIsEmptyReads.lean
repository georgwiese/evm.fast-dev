import InitECandidate.Solver.Mpt.AccountIsEmptyProgram
import InitECandidate.Solver.Mpt.AccountObjectGeometry

namespace InitECandidate.Solver.Mpt.AccountIsEmpty
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem scalar_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (account : BitVec 64)
    (image : AccountDecode.Image source account) (offset : Nat) (inside : offset + 8 ≤ 56) (aligned : offset % 8 = 0)
    (aLocal : source.locals.lookup (ofString "a") = some (.val (.word account))) :
    eval source (field (BitVec.ofNat 64 offset)) =
      some (.val (.word (MemoryBytes.wordBits (source.memory (account + BitVec.ofNat 64 offset))))) := by
  have mapped : source.memaddrs (account + BitVec.ofNat 64 offset) := by
    rw [image.domain]
    exact image.output.word_mapped account offset inside aligned
  cases cell : source.memory (account + BitVec.ofNat 64 offset) with
  | word word =>
    simp [eval,field,localVar,evalHOLExact,evalListHOLExact,toExact,aLocal,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,mapped,cell,MemoryBytes.wordBits]

theorem balance_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (account : BitVec 64)
    (image : AccountDecode.Image source account)
    (aLocal : source.locals.lookup (ofString "a") = some (.val (.word account))) :
    eval source (field 8#64 Input.RlpWrite.U256Value.tupleShape) =
      some (Input.RlpWrite.U256Value.tuple (Input.RlpWrite.U256Value.memoryWords source (account + 8#64))) := by
  apply Input.RlpWrite.U256Value.load
  · simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,aLocal,valueIsWord,valueWord,wordOpHOL,wordOp]
  · intro index
    rw [image.domain]
    have bound := index.isLt
    simpa [BitVec.ofNat_add,BitVec.add_assoc] using image.output.word_mapped account (8 + 8 * index.val) (by omega) (by omega)

theorem compare_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (account emptyHash : BitVec 64)
    (image : AccountDecode.Image source account)
    (aLocal : source.locals.lookup (ofString "a") = some (.val (.word account)))
    (emptyGlobal : source.globals.lookup (ofString "empty_code_hash") = some (.val (.word emptyHash))) :
    evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query))
      [field 48#64, .var .global (ofString "empty_code_hash"), .const 32#64] =
      some (MutableTable.MemeqByteRuntime.values image.hash emptyHash 32) := by
  classical
  have read := scalar_read source account image 48 (by decide) (by decide) aLocal
  rw [image.hashStored] at read
  simp only [MemoryBytes.wordBits] at read
  simp [evalListHOLFinite,evalListHOLExact,show evalHOLExact (toExact source) (field 48#64) = some (.val (.word image.hash)) from read,
    evalHOLExact,toExact,emptyGlobal,MutableTable.MemeqByteRuntime.values]

theorem nonce_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (nonce : BitVec 64)
    (read : eval source (field 0#64) = some (.val (.word nonce))) :
    evaluateHOLFiniteState source body =
      if nonce = 0#64 then evaluateHOLFiniteState source compare
      else (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite source) := by
  classical
  have actual : evalHOLExact (toExact source) (field 0#64) = some (.val (.word nonce)) := read
  by_cases zero : nonce = 0#64
  all_goals simp [body_shape,evaluateHOLFiniteState_seq,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,
    evaluateHOLFiniteState_skip,evalHOLExact,actual,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero,fixClockHOLFinite,
    shapeOfHOLExact,sizeOfShapeWithContextHOL,emptyLocalsHOLFinite]

theorem compare_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (answer : BitVec 64)
    (eqLocal : source.locals.lookup (ofString "eq") = some (.val (.word answer))) :
    evaluateHOLFiniteState source afterCompare =
      if answer = 0#64 then (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite source)
      else evaluateHOLFiniteState source balanceTail := by
  classical
  by_cases zero : answer = 0#64
  all_goals simp [afterCompare,evaluateHOLFiniteState_seq,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,
    evaluateHOLFiniteState_skip,evalHOLExact,localVar,toExact,eqLocal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero,
    fixClockHOLFinite,shapeOfHOLExact,sizeOfShapeWithContextHOL,emptyLocalsHOLFinite]

end InitECandidate.Solver.Mpt.AccountIsEmpty

#print axioms InitECandidate.Solver.Mpt.AccountIsEmpty.scalar_read
#print axioms InitECandidate.Solver.Mpt.AccountIsEmpty.balance_read
#print axioms InitECandidate.Solver.Mpt.AccountIsEmpty.compare_arguments
#print axioms InitECandidate.Solver.Mpt.AccountIsEmpty.nonce_dispatch
#print axioms InitECandidate.Solver.Mpt.AccountIsEmpty.compare_dispatch
