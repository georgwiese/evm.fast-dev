import InitECandidate.Solver.WitnessRadix.QueryLeafCall

namespace InitECandidate.Solver.WitnessRadix.QueryLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

noncomputable local instance : DecidableEq ByteKeys.Key := Classical.decEq _

theorem declaration_return {F : Type} (source : PanSemStateFiniteExact 64 F)
    (name : String) (expression : ExpHOL 64) (continuation : ProgHOL 64)
    (word : BitVec 64) (value : ValueHOL 64) (paid : Nat)
    (readWord : eval source expression = some (.val (.word word)))
    (returned : (evaluateHOLFiniteState (bind source name word) continuation).1 = some (.returned value))
    (frame : emptyLocalsHOLFinite (evaluateHOLFiniteState (bind source name word) continuation).2 =
      emptyLocalsHOLFinite { bind source name word with clock := source.clock - paid }) :
    (evaluateHOLFiniteState source (.dec (ofString name) .one expression continuation)).1 =
        some (.returned value) ∧
    emptyLocalsHOLFinite (evaluateHOLFiniteState source
      (.dec (ofString name) .one expression continuation)).2 =
      emptyLocalsHOLFinite { source with clock := source.clock - paid } := by
  classical
  simp only [eval] at readWord
  rw [evaluateHOLFiniteState_dec_total]
  simp only [readWord, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (evaluateHOLFiniteState (bind source name word) continuation).1 = _ ∧ _
  refine ⟨returned, ?_⟩
  change emptyLocalsHOLFinite (evaluateHOLFiniteState (bind source name word) continuation).2 = _
  exact frame

structure LeafCells {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table keys vals ordinal record pointer length : BitVec 64) : Prop where
  keysMapped : source.memaddrs (table + 32#64)
  keysWord : source.memory (table + 32#64) = .word keys
  valsMapped : source.memaddrs (table + 40#64)
  valsWord : source.memory (table + 40#64) = .word vals
  recordMapped : source.memaddrs (vals + ordinal * 8#64)
  recordWord : source.memory (vals + ordinal * 8#64) = .word record
  pointerMapped : source.memaddrs record
  lengthMapped : source.memaddrs (record + 8#64)
  pointerWord : source.memory record = .word pointer
  lengthWord : source.memory (record + 8#64) = .word length

/-- One complete actual leaf body, including both declarations, the fixed
memeq call and the returned slice. No successful execution is a premise. -/
theorem leaf_return {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table keys vals hash record pointer length : BitVec 64) (ordinal : Nat)
    (left right : ByteKeys.Key) (small : ordinal < 2 ^ 63)
    (node : source.locals.lookup (ofString "node") = some (.val (.word (WordBits.leafTag ordinal))))
    (db : source.locals.lookup (ofString "db") = some (.val (.word table)))
    (hashLocal : source.locals.lookup (ofString "hash") = some (.val (.word hash)))
    (code : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (cells : LeafCells source table keys vals (BitVec.ofNat 64 ordinal) record pointer length)
    (leftView : MemoryBytes.ByteView source (keys + BitVec.ofNat 64 ordinal * 32#64) left)
    (rightView : MemoryBytes.ByteView source hash right)
    (leftFits : (keys + BitVec.ofNat 64 ordinal * 32#64).toNat + 32 < 2 ^ 64)
    (rightFits : hash.toNat + 32 < 2 ^ 64)
    (little : source.be = false) (enough : 5 ≤ source.clock) :
    ∃ paid, paid ≤ 5 ∧
      (evaluateHOLFiniteState source leafCode).1 =
        some (.returned (if left = right then found pointer length else QueryEmpty.zeros)) ∧
      emptyLocalsHOLFinite (evaluateHOLFiniteState source leafCode).2 =
        emptyLocalsHOLFinite { source with clock := source.clock - paid } := by
  classical
  let ordinalState := bind source "ordinal" (BitVec.ofNat 64 ordinal)
  let keysState := bind ordinalState "keys" keys
  have names : ofString "db" ≠ ofString "ordinal" ∧ ofString "hash" ≠ ofString "ordinal" ∧
      ofString "db" ≠ ofString "keys" ∧ ofString "hash" ≠ ofString "keys" ∧
      ofString "ordinal" ≠ ofString "keys" := by decide
  have dbOrdinal : ordinalState.locals.lookup (ofString "db") = some (.val (.word table)) := by
    simp [ordinalState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, db,
      Ne.symm names.1]
  have dbKeys : keysState.locals.lookup (ofString "db") = some (.val (.word table)) := by
    simp [keysState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, dbOrdinal,
      Ne.symm names.2.2.1]
  have hashKeys : keysState.locals.lookup (ofString "hash") = some (.val (.word hash)) := by
    simp [keysState, ordinalState, QueryBranch.bind, setVarHOLFinite,
      HolFiniteMapExact.update, FUPDATE, hashLocal, Ne.symm names.2.1, Ne.symm names.2.2.2.1]
  have ordinalKeys : keysState.locals.lookup (ofString "ordinal") =
      some (.val (.word (BitVec.ofNat 64 ordinal))) := by
    simp [keysState, ordinalState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      Ne.symm names.2.2.2.2]
  have keysKeys : keysState.locals.lookup (ofString "keys") = some (.val (.word keys)) := by
    simp [keysState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have leftKeys := MemoryBytes.byteView_of_fields source keysState rfl rfl rfl _ _ leftView
  have rightKeys := MemoryBytes.byteView_of_fields source keysState rfl rfl rfl _ _ rightView
  obtain ⟨paid, bound, returned, frame⟩ := comparison_return keysState table keys vals
    (BitVec.ofNat 64 ordinal) hash record pointer length left right dbKeys keysKeys ordinalKeys hashKeys
    code leftKeys rightKeys leftFits rightFits little enough cells.valsMapped cells.valsWord
    cells.recordMapped cells.recordWord cells.pointerMapped cells.lengthMapped
    cells.pointerWord cells.lengthWord
  have keysRead := read_keys ordinalState table keys dbOrdinal cells.keysMapped cells.keysWord
  have keysResult := declaration_return ordinalState "keys" keysExpression comparisonCall keys
    (if left = right then found pointer length else QueryEmpty.zeros) (paid + 1) keysRead returned frame
  have ordinalResult := declaration_return source "ordinal" ordinalExpression
    (.dec (ofString "keys") .one keysExpression comparisonCall) (BitVec.ofNat 64 ordinal)
    (if left = right then found pointer length else QueryEmpty.zeros) (paid + 1)
    (read_ordinal source ordinal small node) keysResult.1 keysResult.2
  refine ⟨paid + 1, by omega, ?_⟩
  rw [leaf_shape]
  exact ordinalResult

end InitECandidate.Solver.WitnessRadix.QueryLeaf

#print axioms InitECandidate.Solver.WitnessRadix.QueryLeaf.leaf_return
