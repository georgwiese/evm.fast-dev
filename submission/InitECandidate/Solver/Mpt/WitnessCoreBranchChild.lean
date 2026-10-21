import InitECandidate.Solver.Mpt.WitnessCoreReturnProgram
import InitECandidate.Solver.Mpt.WitnessRecordChild

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Execute the actual original child store using the real current record
node/index and returned child word. Mapping and row preservation follow
from physical ownership; no successful future store is an assumption. -/
theorem branch_child_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db node child : BitVec 64)
    (data : WitnessRecord.Description) (index : Fin 16) (occupied : Fin 17)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word node)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index.val))))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child))) :
    evaluateHOLFiniteState source (.store branchChildAddress (localVar "result"))=
      (none,{source with memory:=StoreWord.put source.memory (WitnessRecord.childAddress node index) child}) := by
  have product : BitVec.ofNat 64 index.val*8#64=BitVec.ofNat 64 (8*index.val):=by
    rw [←BitVec.ofNat_mul]
    congr 1
    omega
  have addressRead : eval source branchChildAddress=some (.val (.word (WitnessRecord.childAddress node index))):=by
    simp [eval,branchChildAddress,WitnessRecord.childAddress,byteAddress,evalHOLExact,evalListHOLExact,localVar,toExact,branchCell,indexCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,product,BitVec.ofNat_add,BitVec.add_assoc]
  have childRead : eval source (localVar "result")=some (.val (.word child)):=by
    simp [eval,evalHOLExact,localVar,toExact,resultCell]
  exact StoreWord.execute source branchChildAddress (localVar "result") (WitnessRecord.childAddress node index) child addressRead childRead
    (view.branch_child_mapped source record db node data index occupied payload)

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_child_execute
