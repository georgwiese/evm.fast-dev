import InitECandidate.Solver.MutableTable.MemoryModelInsert
import InitECandidate.Solver.MutableTable.MemoryModelFields
import InitECandidate.Solver.MutableTable.MemoryModelEntry

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- Actual raw-insertion caller, including the selected empty slot and the
post-call dense order/inverse-position model. This is the induction step for
rehashing; entry ownership and query/code/clock reachability remain explicit. -/
theorem insertion_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (valid : Valid kind plan) (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity)
    (header : Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (occupied : Occupied source kind plan slots)
    (query value : BitVec 64) (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some (TableCall.values (cell plan .header 0) query value))
    (enough : slots.length + KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 2 ≤ source.clock) :
    ∃ paid index, paid ≤ slots.length + KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 2 ∧
      index.toNat < plan.capacity ∧ index.toNat ∉ slots ∧
      evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_insert_raw") arguments) =
        (none, {source with memory := (insertedMemory source.memory source.be kind plan query index (BitVec.ofNat 64 slots.length) value), clock := source.clock - paid}) ∧
      Header (insertedMemory source.memory source.be kind plan query index (BitVec.ofNat 64 slots.length) value)
        kind plan (BitVec.ofNat 64 (slots ++ [index.toNat]).length) ∧
      Occupied {source with memory := (insertedMemory source.memory source.be kind plan query index (BitVec.ofNat 64 slots.length) value), clock := source.clock - paid}
        kind plan (slots ++ [index.toNat]) := by
  have data := runtime_data source kind plan valid domain query slots room header occupied bits small power queryFits queryMapped little hashCode copyCode
  obtain ⟨paid, index, bounded, inside, actual, _, empty⟩ := Insert.general_call source (cell plan .header 0) (parameters kind plan query) kind
    (cell plan .values 0) (cell plan .order 0) (cell plan .position 0) (BitVec.ofNat 64 slots.length) value bits slots data insertCode arguments args enough
  have capNat : (parameters kind plan query).capacity.toNat = plan.capacity := by
    change (BitVec.ofNat 64 plan.capacity).toNat = plan.capacity
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (capacity_small kind plan valid)]
  rw [capNat] at inside
  have fresh := empty_slot_fresh source kind plan slots occupied index inside empty
  have countInside : (BitVec.ofNat 64 slots.length).toNat < plan.capacity := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans room (capacity_small kind plan valid))]
    exact room
  have nextHeader := Header.after_insert source.memory source.be kind plan valid query index (BitVec.ofNat 64 slots.length) value inside countInside header
  have nextOccupied := Occupied.after_insert source kind plan valid domain little slots room occupied query index value inside empty
  refine ⟨paid, index, bounded, inside, fresh, actual, ?_, ?_⟩
  · simpa only [List.length_append, List.length_singleton, BitVec.ofNat_add] using nextHeader
  · exact Occupied.of_fields _ _ kind plan _ nextOccupied rfl rfl rfl

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.insertion_call
