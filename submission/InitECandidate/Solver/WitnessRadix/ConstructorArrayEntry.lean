import InitECandidate.Solver.WitnessRadix.ConstructorData

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact BackingLayout
open Flapjack.Basis.Pure.MlString QueryBranch

def arrayBindings : List (String × ExpHOL 64) :=
  [("keys", BuildEntry.header 32#64), ("vals", BuildEntry.header 40#64),
   ("order", BuildEntry.header 56#64), ("i", .const 0#64)]
def arrayEntry {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) : PanSemStateFiniteExact 64 F :=
  bind (bind (bind (bind source "keys" layout.keys) "vals" layout.vals) "order" layout.primary) "i" 0#64

theorem array_lookup_other {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) (name : String)
    (keyNe : ofString "keys" ≠ ofString name) (valNe : ofString "vals" ≠ ofString name)
    (orderNe : ofString "order" ≠ ofString name) (indexNe : ofString "i" ≠ ofString name) :
    (arrayEntry source layout).locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
  unfold arrayEntry
  rw [bind_lookup_other _ "i" name _ indexNe, bind_lookup_other _ "order" name _ orderNe,
    bind_lookup_other _ "vals" name _ valNe, bind_lookup_other _ "keys" name _ keyNe]

theorem table_tail_shape : tableTail = BuildEntry.declarations arrayBindings (.seq recordLoop afterRecords) := rfl

theorem header_read {F : Type} (source : PanSemStateFiniteExact 64 F) (table offset value : BitVec 64)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (mapped : source.memaddrs (table + offset)) (stored : source.memory (table + offset) = .word value) :
    eval source (BuildEntry.header offset) = some (.val (.word value)) := by
  simp [eval, BuildEntry.header, addConst, localVar, evalHOLExact, evalListHOLExact, toExact,
    tableLocal, mapped, stored, isWfShapeExactHOL, memLoadHOLExact, valueIsWord, valueWord, wordOpHOL, wordOp]

theorem array_initialize {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word layout.table)))
    (header : BuildEntry.Header source layout.table layout.keys layout.vals layout.primary layout.backup) :
    ∃ restoreStack, BuildEntry.Initializes source arrayBindings (arrayEntry source layout) restoreStack := by
  let keys := bind source "keys" layout.keys
  let vals := bind keys "vals" layout.vals
  let order := bind vals "order" layout.primary
  have tableKeys : keys.locals.lookup (ofString "t") = some (.val (.word layout.table)) :=
    (bind_lookup_other source "keys" "t" _ (by decide)).trans tableLocal
  have tableVals : vals.locals.lookup (ofString "t") = some (.val (.word layout.table)) :=
    (bind_lookup_other keys "vals" "t" _ (by decide)).trans tableKeys
  have keyRead := header_read source layout.table 32#64 layout.keys tableLocal header.keysMapped header.keysWord
  have valRead := header_read keys layout.table 40#64 layout.vals tableKeys header.valsMapped header.valsWord
  have orderRead := header_read vals layout.table 56#64 layout.primary tableVals header.srcMapped header.srcWord
  exact ⟨_, .step layout.keys keyRead (.step layout.vals valRead (.step layout.primary orderRead (.step 0#64 rfl (.done _))))⟩

theorem array_locals {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (recordsLocal : source.locals.lookup (ofString "slice_arr") = some (.val (.word layout.records))) :
    Locals (arrayEntry source layout) layout.keys layout.vals layout.primary layout.records 0#64 := by
  let keys := bind source "keys" layout.keys
  let vals := bind keys "vals" layout.vals
  let order := bind vals "order" layout.primary
  have other (name : String) (keyNe : ofString "keys" ≠ ofString name) (valNe : ofString "vals" ≠ ofString name)
      (orderNe : ofString "order" ≠ ofString name) (indexNe : ofString "i" ≠ ofString name) :
      (arrayEntry source layout).locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
    change (bind order "i" 0#64).locals.lookup _ = _
    rw [bind_lookup_other order "i" name _ indexNe, bind_lookup_other vals "order" name _ orderNe,
      bind_lookup_other keys "vals" name _ valNe, bind_lookup_other source "keys" name _ keyNe]
  refine ⟨?_, ?_, ?_, (other "slice_arr" (by decide) (by decide) (by decide) (by decide)).trans recordsLocal,
    bind_lookup_same _ _ _⟩
  · change (bind order "i" 0#64).locals.lookup _ = _
    rw [bind_lookup_other order "i" "keys" _ (by decide), bind_lookup_other vals "order" "keys" _ (by decide),
      bind_lookup_other keys "vals" "keys" _ (by decide)]
    exact bind_lookup_same _ _ _
  · change (bind order "i" 0#64).locals.lookup _ = _
    rw [bind_lookup_other order "i" "vals" _ (by decide), bind_lookup_other vals "order" "vals" _ (by decide)]
    exact bind_lookup_same _ _ _
  · change (bind order "i" 0#64).locals.lookup _ = _
    rw [bind_lookup_other order "i" "order" _ (by decide)]
    exact bind_lookup_same _ _ _

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.array_initialize
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.array_locals
