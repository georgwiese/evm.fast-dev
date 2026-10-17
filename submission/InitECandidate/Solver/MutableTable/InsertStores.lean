import InitECandidate.Solver.MutableTable.InsertCount
import InitECandidate.Solver.MutableTable.ByteStoreExec

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

theorem value_store (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table vals index value : BitVec 64)
    (tLocal : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (iLocal : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (valueLocal : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (valsMapped : source.memaddrs (table+40#64)) (valsCell : source.memory (table+40#64)=.word vals)
    (mapped : source.memaddrs (vals+index*8#64)) :
    evaluateHOLFiniteState source valueStore=(none,{source with memory:=StoreWord.put source.memory (vals+index*8#64) value}) := by
  have valsRead:=Find.table_read source table 40#64 vals tLocal valsMapped valsCell
  apply StoreWord.execute source _ _ _ value _ _ mapped
  · simp only [eval] at valsRead ⊢
    simp [valueStore,scaled,localVar,evalHOLExact,evalListHOLExact,toExact,iLocal,valsRead,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
  · simp [eval,localVar,evalHOLExact,toExact,valueLocal]

theorem used_store (source : PanSemStateFiniteExact 64 Guest.HostMemory) (used index : BitVec 64)
    (usedLocal : source.locals.lookup (ofString "used")=some (.val (.word used)))
    (iLocal : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (mapped : source.memaddrs (panByteAlignHOL (width:=64) (used+index))) (little : source.be=false) :
    evaluateHOLFiniteState source usedStore=(none,{source with memory:=ByteStore.write source.memory (used+index) 1}) := by
  apply ByteStore.execute source _ _ (used+index) 1 _ _ mapped little
  · simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,usedLocal,iLocal,valueIsWord,valueWord,wordOpHOL,wordOp]
  · rfl

def suffixMemory (memory : WordWrites.Memory) (table vals used order position index count value : BitVec 64) : WordWrites.Memory:=
  WordWrites.write (ByteStore.write (StoreWord.put memory (vals+index*8#64) value) (used+index) 1)
    (countWrites table order position index count)

/-- The complete real suffix after memcpy: value, used byte, order,
order-position and count writes, with exact memory and return behavior. -/
theorem after_copy (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table vals used order position index count value : BitVec 64)
    (tLocal : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (iLocal : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (valueLocal : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (usedLocal : source.locals.lookup (ofString "used")=some (.val (.word used)))
    (orderLocal : source.locals.lookup (ofString "order")=some (.val (.word order)))
    (positionLocal : source.locals.lookup (ofString "order_pos")=some (.val (.word position)))
    (valsMapped : source.memaddrs (table+40#64)) (valsCell : source.memory (table+40#64)=.word vals)
    (valueMapped : source.memaddrs (vals+index*8#64))
    (usedMapped : source.memaddrs (panByteAlignHOL (width:=64) (used+index)))
    (orderMapped : source.memaddrs (order+count*8#64)) (positionMapped : source.memaddrs (position+index*8#64))
    (countMapped : source.memaddrs (table+24#64)) (countCell : source.memory (table+24#64)=.word count)
    (awayValue : table+24#64≠vals+index*8#64)
    (awayUsed : table+24#64≠panByteAlignHOL (width:=64) (used+index)) (little : source.be=false) :
    ∃ target,evaluateHOLFiniteState source afterCopy=(some (.returned (.val (.word 0#64))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite
        {source with memory:=suffixMemory source.memory table vals used order position index count value} := by
  let valued:={source with memory:=StoreWord.put source.memory (vals+index*8#64) value}
  let flagged:={valued with memory:=ByteStore.write valued.memory (used+index) 1}
  have valueRun:=value_store source table vals index value tLocal iLocal valueLocal valsMapped valsCell valueMapped
  have usedRun:=used_store valued used index usedLocal iLocal usedMapped little
  have keptCount : flagged.memory (table+24#64)=.word count := by
    simpa only [flagged,valued,ByteStore.write,StoreWord.put,if_neg awayUsed,if_neg awayValue] using countCell
  obtain ⟨target,tailRun,frame⟩:=after_used flagged table order position index count tLocal orderLocal positionLocal iLocal
    orderMapped positionMapped countMapped keptCount
  refine ⟨target,?_,frame⟩
  rw [afterCopy,StateSteps.next_sequence source valued valueStore _ valueRun (Nat.le_refl _),
    StateSteps.next_sequence valued flagged usedStore _ usedRun (Nat.le_refl _)]
  exact tailRun

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.value_store
#print axioms InitECandidate.Solver.MutableTable.Insert.used_store
#print axioms InitECandidate.Solver.MutableTable.Insert.after_copy
