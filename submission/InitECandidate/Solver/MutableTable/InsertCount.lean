import InitECandidate.Solver.MutableTable.InsertProgram
import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def countWrites (table order position index count : BitVec 64) : List (BitVec 64×BitVec 64):=
  [(order+count*8#64,index),(position+index*8#64,count),(table+24#64,count+1#64)]

/-- Exact order, order-position and count stores, followed by the literal
zero return. All three stores are real source operations. -/
theorem after_count (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table order position index count : BitVec 64)
    (tLocal : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (orderLocal : source.locals.lookup (ofString "order")=some (.val (.word order)))
    (positionLocal : source.locals.lookup (ofString "order_pos")=some (.val (.word position)))
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (orderMapped : source.memaddrs (order+count*8#64)) (positionMapped : source.memaddrs (position+index*8#64))
    (countMapped : source.memaddrs (table+24#64)) :
    evaluateHOLFiniteState source afterCount=(some (.returned (.val (.word 0#64))),
      emptyLocalsHOLFinite {source with memory:=WordWrites.write source.memory (countWrites table order position index count)}) := by
  classical
  simp [afterCount,orderStore,positionStore,countStore,returnZero,scaled,localVar,
    evaluateHOLFiniteState_seq,evaluateHOLFiniteState_store,evaluateHOLFiniteState_return,
    evalHOLExact,evalListHOLExact,toExact,tLocal,orderLocal,positionLocal,indexLocal,countLocal,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,flattenHOL,panMemStoresHOL,panMemStoreHOL,
    orderMapped,positionMapped,countMapped,shapeOfHOLExact,sizeOfShapeWithContextHOL,
    fixClockHOLFinite,countWrites,WordWrites.write,StoreWord.put]
  rfl

/-- Actual count declaration and its lexical scope around the final stores. -/
theorem after_used (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table order position index count : BitVec 64)
    (tLocal : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (orderLocal : source.locals.lookup (ofString "order")=some (.val (.word order)))
    (positionLocal : source.locals.lookup (ofString "order_pos")=some (.val (.word position)))
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (orderMapped : source.memaddrs (order+count*8#64)) (positionMapped : source.memaddrs (position+index*8#64))
    (countMapped : source.memaddrs (table+24#64)) (countCell : source.memory (table+24#64)=.word count) :
    ∃ target,evaluateHOLFiniteState source afterUsed=(some (.returned (.val (.word 0#64))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite
        {source with memory:=WordWrites.write source.memory (countWrites table order position index count)} := by
  let entered:=bind source "n" count
  have run:=after_count entered table order position index count
    ((bind_lookup_other _ "n" "t" _ (by decide)).trans tLocal)
    ((bind_lookup_other _ "n" "order" _ (by decide)).trans orderLocal)
    ((bind_lookup_other _ "n" "order_pos" _ (by decide)).trans positionLocal)
    ((bind_lookup_other _ "n" "i" _ (by decide)).trans indexLocal)
    (bind_lookup_same _ _ _) orderMapped positionMapped countMapped
  have scopedRun:=Input.ScalarScope.declare_execute source _ "n" (Find.tableLoad 24#64) count afterCount
    (some (.returned (.val (.word 0#64))))
    (Find.table_read source table 24#64 count tLocal countMapped countCell) run
  refine ⟨_,scopedRun,?_⟩
  rfl

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.after_count
#print axioms InitECandidate.Solver.MutableTable.Insert.after_used
