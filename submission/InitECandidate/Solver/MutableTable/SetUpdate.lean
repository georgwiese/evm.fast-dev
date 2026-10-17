import InitECandidate.Solver.MutableTable.SetProgram
import InitECandidate.Solver.MutableTable.InsertStores

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- An existing-key setter branch performs exactly one value store and
returns before the grow/insert code. -/
theorem update_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table vals index capacity value : BitVec 64)
    (tLocal : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (iLocal : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (valueLocal : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (capMapped : source.memaddrs (table+16#64)) (capCell : source.memory (table+16#64)=.word capacity)
    (valsMapped : source.memaddrs (table+40#64)) (valsCell : source.memory (table+40#64)=.word vals)
    (mapped : source.memaddrs (vals+index*8#64)) (different : index≠capacity) :
    evaluateHOLFiniteState source afterIndex=(some (.returned (.val (.word 0#64))),
      emptyLocalsHOLFinite {source with memory:=StoreWord.put source.memory (vals+index*8#64) value}) := by
  let post:={source with memory:=StoreWord.put source.memory (vals+index*8#64) value}
  have storeRun:=Insert.value_store source table vals index value tLocal iLocal valueLocal valsMapped valsCell mapped
  have branchRun : evaluateHOLFiniteState source updateBranch=
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite post) := by
    rw [updateBranch,StateSteps.next_sequence source post Insert.valueStore Insert.returnZero storeRun (Nat.le_refl _)]
    simp [Insert.returnZero,evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have capRead:=Find.table_read source table 16#64 capacity tLocal capMapped capCell
  simp only [eval] at capRead
  have selected : evaluateHOLFiniteState source (.ite presentTest updateBranch .skip)=
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite post) := by
    simp [evaluateHOLFiniteState_ite,presentTest,localVar,evalHOLExact,toExact,iLocal,capRead,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,different,branchRun]
  rw [afterIndex,StateSteps.stopped_sequence source (emptyLocalsHOLFinite post) _ _ _ selected (Nat.le_refl _)]

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.update_execute
