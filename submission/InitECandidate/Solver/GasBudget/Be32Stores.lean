import InitECandidate.Solver.GasBudget.MemoryWriterProgram
import InitECandidate.Solver.WitnessRadix.ByteStoreWord
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.GasBudget.Be32Stores
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def address (offset : Nat) : ExpHOL 64 := if offset = 0 then localVar "p" else .op .add [localVar "p", .const (BitVec.ofNat 64 offset)]
def byteValue (bits : Nat) : ExpHOL 64 := if bits = 0 then localVar "v" else .shift .lsr (localVar "v") (.const (BitVec.ofNat 64 bits))
def stores : List (Nat × Nat) → ProgHOL 64
  | [] => .return (.const 0#64)
  | clause :: rest => .seq (.storeByte (address clause.1) (byteValue clause.2)) (stores rest)
def clauses : List (Nat × Nat) := [(0, 24), (1, 16), (2, 8), (3, 0)]
def written (memory : WordWrites.Memory) (be : Bool) (pointer value : BitVec 64) : List (Nat × Nat) → WordWrites.Memory
  | [] => memory
  | clause :: rest => written (ByteStore.put memory be (pointer + BitVec.ofNat 64 clause.1) (BitVec.ofNat 8 (value >>> clause.2).toNat)) be pointer value rest

theorem original_body : MemoryWriter.Kind.be32.body = stores clauses := by
  simp [MemoryWriter.Kind.body, MemoryWriter.Kind.signature, MemoryWriter.Kind.original, Guest.guestFn_st_be32,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, stores, clauses, address, byteValue,
    localVar, ↓reduceIte]

theorem read_address (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat)
    (binding : source.locals.lookup (ofString "p") = some (.val (.word pointer))) :
    eval source (address offset) = some (.val (.word (pointer + BitVec.ofNat 64 offset))) := by
  by_cases zero : offset = 0
  all_goals simp [address, zero, eval, evalHOLExact, evalListHOLExact, toExact, localVar, binding, valueIsWord, valueWord, wordOpHOL, wordOp]

theorem read_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64) (bits : Nat)
    (binding : source.locals.lookup (ofString "v") = some (.val (.word value))) (small : bits < 64) :
    eval source (byteValue bits) = some (.val (.word (value >>> bits))) := by
  have number : bits % 18446744073709551616 = bits := Nat.mod_eq_of_lt (by omega)
  by_cases zero : bits = 0
  all_goals simp [byteValue, zero, eval, evalHOLExact, toExact, localVar, binding, wordShiftHOL, BitVec.toNat_ofNat, number, small]

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer value : BitVec 64) (commands : List (Nat × Nat))
    (pointerLocal : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (valueLocal : source.locals.lookup (ofString "v") = some (.val (.word value)))
    (small : ∀ clause ∈ commands, clause.2 < 64)
    (mapped : ∀ clause ∈ commands, source.memaddrs (panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 clause.1))) :
    evaluateHOLFiniteState source (stores commands) = (some (.returned (.val (.word 0#64))),
      emptyLocalsHOLFinite {source with memory := written source.memory source.be pointer value commands}) := by
  induction commands generalizing source with
  | nil => simp [stores, written, evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  | cons clause rest ih =>
    let stored := {source with memory := ByteStore.put source.memory source.be (pointer + BitVec.ofNat 64 clause.1) (BitVec.ofNat 8 (value >>> clause.2).toNat)}
    have actual := ByteStore.execute_word source (address clause.1) (byteValue clause.2) (pointer + BitVec.ofNat 64 clause.1) (value >>> clause.2)
      (read_address source pointer clause.1 pointerLocal) (read_value source value clause.2 valueLocal (small clause (by simp))) (mapped clause (by simp))
    have tail := ih stored pointerLocal valueLocal (by intro next member; exact small next (by simp [member]))
      (by intro next member; exact mapped next (by simp [member]))
    rw [stores, StateSteps.next_sequence source stored _ (stores rest) actual (Nat.le_refl _)]
    exact tail

theorem written_away (memory : WordWrites.Memory) (be : Bool) (pointer value query : BitVec 64) (commands : List (Nat × Nat))
    (outside : ∀ clause ∈ commands, query ≠ panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 clause.1)) :
    written memory be pointer value commands query = memory query := by
  induction commands generalizing memory with
  | nil => rfl
  | cons clause rest ih =>
    rw [written, ih _ (by intro next member; exact outside next (by simp [member]))]
    exact ByteStore.away memory be _ query _ (outside clause (by simp))

end InitECandidate.Solver.GasBudget.Be32Stores

#print axioms InitECandidate.Solver.GasBudget.Be32Stores.original_body
#print axioms InitECandidate.Solver.GasBudget.Be32Stores.execute
#print axioms InitECandidate.Solver.GasBudget.Be32Stores.written_away
