import InitECandidate.Solver.MutableTable.MemoryModel

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- The concrete physical representation discharges all table-side runtime
entry conditions of the checked raw-insertion/query/setter contracts. Query
ownership, actual table reachability and the count/order invariant still
require proof from constructors and mutations. -/
theorem runtime_data (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (valid : Valid kind plan) (domain : source.memaddrs = InitE.ordinaryDomain) (query : BitVec 64)
    (slots : List Nat) (room : slots.length < plan.capacity)
    (header : Header source.memory kind plan (BitVec.ofNat 64 slots.length))
    (occupied : Occupied source kind plan slots) (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (little : source.be = false)
    (hashCode : source.code.lookup (Flapjack.Basis.Pure.MlString.ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (Flapjack.Basis.Pure.MlString.ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one)) :
    Insert.GeneralData source (cell plan .header 0) (parameters kind plan query) kind
      (cell plan .values 0) (cell plan .order 0) (cell plan .position 0) (BitVec.ofNat 64 slots.length) bits slots := by
  have mappedHeader (offset : Nat) (inside : offset < 72) (aligned : offset % 8 = 0) :
      source.memaddrs (cell plan .header 0 + BitVec.ofNat 64 offset) := by
    rw [domain, constant_cell]
    exact mapped kind plan valid .header offset inside aligned
  have read (offset : Nat) (value : BitVec 64) (member : (offset, value) ∈ headerEntries kind plan (BitVec.ofNat 64 slots.length)) :
      source.memory (cell plan .header 0 + BitVec.ofNat 64 offset) = .word value := by
    rw [constant_cell]
    exact header offset value member
  have capNumber : (parameters kind plan query).capacity.toNat = plan.capacity := by
    change (BitVec.ofNat 64 plan.capacity).toNat = plan.capacity
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (capacity_small kind plan valid)]
  have countInside : (BitVec.ofNat 64 slots.length).toNat < plan.capacity := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans room (capacity_small kind plan valid))]
    exact room
  refine {
    header := Header.find_data source kind plan valid domain query _ header
    keyLength := rfl
    small := small
    capacity := by change BitVec.ofNat 64 plan.capacity = _; rw [power]
    room := by rwa [← power]
    binary := ?_
    covered := ?_
    orderMapped := mappedHeader 56 (by decide) (by decide)
    orderCell := read 56 _ (by simp [headerEntries])
    positionMapped := mappedHeader 64 (by decide) (by decide)
    positionCell := read 64 _ (by simp [headerEntries])
    valsMapped := mappedHeader 40 (by decide) (by decide)
    valsCell := read 40 _ (by simp [headerEntries])
    countMapped := mappedHeader 24 (by decide) (by decide)
    countCell := read 24 _ (by simp [headerEntries])
    queryFits := queryFits
    queryMapped := queryMapped
    slots := ?_
    little := little
    hashCode := hashCode
    copyCode := copyCode }
  · intro index inside
    have actual : Find.usedByte source (parameters kind plan query) (BitVec.ofNat 64 index) = some (if index ∈ slots then 1 else 0) :=
      occupied.used index (by rwa [power])
    by_cases member : index ∈ slots
    · exact Or.inr (by simpa only [if_pos member] using actual)
    · exact Or.inl (by simpa only [if_neg member] using actual)
  · intro index inside one
    have actual : Find.usedByte source (parameters kind plan query) (BitVec.ofNat 64 index) = some (if index ∈ slots then 1 else 0) :=
      occupied.used index (by rwa [power])
    by_contra absent
    rw [one] at actual
    simp [absent] at actual
  · intro index inside
    rw [domain]
    exact slot_data kind plan valid query index (BitVec.ofNat 64 slots.length) (by rwa [capNumber] at inside) countInside

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.runtime_data
