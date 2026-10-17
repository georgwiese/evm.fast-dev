import InitECandidate.Solver.MutableTable.MemoryModelSet
import InitECandidate.Solver.MutableTable.MemoryModelEntry
import InitECandidate.Solver.MutableTable.SetNoGrowthCall

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- Actual original no-growth setter call carries the physical representation
forward. The caller supplies its reachable table/query/code and clock facts;
the resulting representation is proved from the executed mutation. -/
theorem setter_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (valid : Valid kind plan) (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : 2 * slots.length + 2 ≤ plan.capacity)
    (header : Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (occupied : Occupied source kind plan slots)
    (query value : BitVec 64) (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (setCode : source.code.lookup (ofString "htab_set") = some (TableCall.formals, Set.body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some (TableCall.values (cell plan .header 0) query value))
    (enough : Set.noGrowthPrice kind slots.length + 1 ≤ source.clock) :
    ∃ paid memory next, paid ≤ Set.noGrowthPrice kind slots.length + 1 ∧
      evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_set") arguments) =
        (none, {source with memory := memory, clock := source.clock - paid}) ∧
      (next = slots ∨ ∃ slot, next = slots ++ [slot]) ∧
      next.length ≤ slots.length + 1 ∧
      Header memory kind plan (BitVec.ofNat 64 next.length) ∧
      Occupied {source with memory := memory, clock := source.clock - paid} kind plan next := by
  have free : slots.length < plan.capacity := by omega
  have data := runtime_data source kind plan valid domain query slots free header occupied bits small power queryFits queryMapped little hashCode copyCode
  have countBound : (BitVec.ofNat 64 slots.length).toNat ≤ slots.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans free (capacity_small kind plan valid))]
  obtain ⟨paid, memory, bounded, actual, _, effect⟩ := Set.no_growth_call source (cell plan .header 0) (parameters kind plan query) kind
    (cell plan .values 0) (cell plan .order 0) (cell plan .position 0) (BitVec.ofNat 64 slots.length) value bits slots data countBound
    (by rwa [← power]) memeqCode findCode insertCode setCode arguments args enough
  obtain ⟨next, shape, nextHeader, nextOccupied⟩ := setter_effect source kind plan valid domain little slots free header occupied query value memory effect
  have lengthBound : next.length ≤ slots.length + 1 := by
    rcases shape with rfl | ⟨slot, rfl⟩ <;> simp
  exact ⟨paid, memory, next, bounded, actual, shape, lengthBound, nextHeader,
    Occupied.of_fields _ _ kind plan next nextOccupied rfl rfl rfl⟩

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.setter_call
