import InitECandidate.Solver.Mpt.BranchValueUpdateProgram

namespace InitECandidate.Solver.Mpt.BranchValueUpdate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def stores (nodeName pointerName sizeName : String) : ProgHOL 64:=
  .seq (.store (addConst (localVar nodeName) 160#64) (localVar pointerName))
    (.store (addConst (localVar nodeName) 168#64) (localVar sizeName))

/-- The literal two-store block used by the original split helpers. -/
theorem stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node pointer size : BitVec 64)
    (nodeName pointerName sizeName : String)
    (nodeCell : source.locals.lookup (ofString nodeName)=some (.val (.word node)))
    (pointerCell : source.locals.lookup (ofString pointerName)=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString sizeName)=some (.val (.word size)))
    (pointerMapped : source.memaddrs (node+160#64)) (sizeMapped : source.memaddrs (node+168#64)) :
    evaluateHOLFiniteState source (stores nodeName pointerName sizeName)=(none,post source node pointer size) := by
  have addressRead (offset : BitVec 64) : eval source (addConst (localVar nodeName) offset)=some (.val (.word (node+offset))):=by
    simp [eval,addConst,localVar,evalHOLExact,evalListHOLExact,toExact,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have pointerRead : eval source (localVar pointerName)=some (.val (.word pointer)):=by
    simp [eval,localVar,evalHOLExact,toExact,pointerCell]
  let middle:={source with memory:=StoreWord.put source.memory (node+160#64) pointer}
  have nextAddress : eval middle (addConst (localVar nodeName) 168#64)=some (.val (.word (node+168#64))):=by
    simpa only [eval,addConst,localVar,evalHOLExact,evalListHOLExact,toExact,middle] using addressRead 168#64
  have sizeRead : eval middle (localVar sizeName)=some (.val (.word size)):=by
    simp [eval,localVar,evalHOLExact,toExact,middle,sizeCell]
  have first:=StoreWord.execute source (addConst (localVar nodeName) 160#64) (localVar pointerName) (node+160#64) pointer (addressRead 160#64) pointerRead pointerMapped
  have second:=StoreWord.execute middle (addConst (localVar nodeName) 168#64) (localVar sizeName) (node+168#64) size nextAddress sizeRead sizeMapped
  rw [stores,evaluateHOLFiniteState_seq_line780,first]
  exact second

end InitECandidate.Solver.Mpt.BranchValueUpdate

#print axioms InitECandidate.Solver.Mpt.BranchValueUpdate.stores_execute
