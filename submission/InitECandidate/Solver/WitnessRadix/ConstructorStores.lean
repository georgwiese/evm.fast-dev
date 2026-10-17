import InitECandidate.Solver.WitnessRadix.ConstructorProgram
import InitECandidate.Solver.WitnessRadix.WordWrites

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

structure Locals {F : Type} (source : PanSemStateFiniteExact 64 F)
    (keys vals order records index : BitVec 64) : Prop where
  keysLocal : source.locals.lookup (ofString "keys") = some (.val (.word keys))
  valsLocal : source.locals.lookup (ofString "vals") = some (.val (.word vals))
  orderLocal : source.locals.lookup (ofString "order") = some (.val (.word order))
  recordsLocal : source.locals.lookup (ofString "slice_arr") = some (.val (.word records))
  indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index))

def recordWrites (vals order records index : BitVec 64) : List (BitVec 64 × BitVec 64) :=
  [(vals + index * 8#64, records + index * 16#64), (order + index * 8#64, index)]

def storesPost {F : Type} (source : PanSemStateFiniteExact 64 F)
    (vals order records index : BitVec 64) : PanSemStateFiniteExact 64 F :=
  bind { source with memory := WordWrites.write source.memory (recordWrites vals order records index) }
    "i" (index + 1#64)

/-- The literal constructor's two record/index stores and increment. -/
theorem stores_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (keys vals order records index : BitVec 64) (locals : Locals source keys vals order records index)
    (valsMapped : source.memaddrs (vals + index * 8#64))
    (orderMapped : source.memaddrs (order + index * 8#64)) :
    evaluateHOLFiniteState source stores = (none, storesPost source vals order records index) := by
  classical
  rcases locals with ⟨keysLocal, valsLocal, orderLocal, recordsLocal, indexLocal⟩
  simp [ofString] at keysLocal valsLocal orderLocal recordsLocal indexLocal
  simp [stores, scaled, localVar, addConst,
    evaluateHOLFiniteState_seq, evaluateHOLFiniteState_assign, evaluateHOLFiniteState_store,
    evalHOLExact, evalListHOLExact, toExact, isValidValueHOLFinite, lookupKvarHOLFinite,
    setKvarHOLFinite, setVarHOLFinite, QueryBranch.bind, HolFiniteMapExact.update, FUPDATE, ofString,
    keysLocal, valsLocal, orderLocal, recordsLocal, indexLocal, valueIsWord, valueWord,
    panOpHOL, wordOpHOL, wordOp, shapeOfHOLExact, shapeEqHOL, flattenHOL,
    panMemStoresHOL, panMemStoreHOL, valsMapped, orderMapped,
    fixClockHOLFinite, storesPost, recordWrites, WordWrites.write, StoreWord.put]
  rfl

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.stores_execute
