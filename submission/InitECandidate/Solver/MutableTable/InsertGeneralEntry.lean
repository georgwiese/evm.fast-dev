import InitECandidate.Solver.MutableTable.InsertGeneralTail
import InitECandidate.Solver.MutableTable.InsertCountScan
import InitECandidate.Solver.MutableTable.InsertPreparedData
import InitECandidate.Solver.MutableTable.InsertLift32
import InitECandidate.Solver.MutableTable.KeyHash
import InitECandidate.Solver.MutableTable.HeaderData

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- Physical destination region and bookkeeping cells for a possible empty
slot. These are ownership/mapping facts, never assumed insertion executions. -/
structure SlotData (domain : BitVec 64 → Prop) (p : Find.Parameters)
    (table vals order position count index : BitVec 64) (width : Nat) : Prop where
  fits : (p.keys + index * p.stride).toNat + width < 2 ^ 64
  mapped : ∀ offset < width, domain (panByteAlignHOL (width := 64) (byteAddress (p.keys + index * p.stride) offset))
  valueMapped : domain (vals + index * 8#64)
  usedMapped : domain (panByteAlignHOL (width := 64) (p.used + index))
  orderMapped : domain (order + count * 8#64)
  positionMapped : domain (position + index * 8#64)
  awayValue : table + 24#64 ≠ vals + index * 8#64
  awayUsed : table + 24#64 ≠ panByteAlignHOL (width := 64) (p.used + index)
  awayValsHeader : CopyGeneral.Away (p.keys + index * p.stride) (table + 40#64) width
  awayCountHeader : CopyGeneral.Away (p.keys + index * p.stride) (table + 24#64) width

/-- Original raw-insertion entry conditions. Mutable table ownership/count
invariants must derive these at actual callers; no phase runtime is assumed. -/
structure GeneralData (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (kind : KeyHash.Kind) (vals order position count : BitVec 64) (bits : Nat) (items : List Nat) : Prop where
  header : Find.HeaderData source table p
  keyLength : p.keyLength = BitVec.ofNat 64 (KeyHash.keySize kind)
  small : bits < 64
  capacity : p.capacity = BitVec.ofNat 64 (2 ^ bits)
  room : items.length < 2 ^ bits
  binary : ∀ i < 2 ^ bits, Find.usedByte source p (BitVec.ofNat 64 i) = some 0 ∨ Find.usedByte source p (BitVec.ofNat 64 i) = some 1
  covered : ∀ i < 2 ^ bits, Find.usedByte source p (BitVec.ofNat 64 i) = some 1 → i ∈ items
  orderMapped : source.memaddrs (table + 56#64)
  orderCell : source.memory (table + 56#64) = .word order
  positionMapped : source.memaddrs (table + 64#64)
  positionCell : source.memory (table + 64#64) = .word position
  valsMapped : source.memaddrs (table + 40#64)
  valsCell : source.memory (table + 40#64) = .word vals
  countMapped : source.memaddrs (table + 24#64)
  countCell : source.memory (table + 24#64) = .word count
  queryFits : p.key.toNat + KeyHash.keySize kind < 2 ^ 64
  queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress p.key offset))
  slots : ∀ index : BitVec 64, index.toNat < p.capacity.toNat → SlotData source.memaddrs p table vals order position count index (KeyHash.keySize kind)
  little : source.be = false
  hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one)
  copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one)

/-- Physical entry data transfers across caller environments and clocks.
All actual nonlocal fields are compared explicitly. -/
theorem GeneralData.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (kind : KeyHash.Kind) (vals order position count : BitVec 64) (bits : Nat) (items : List Nat)
    (data : GeneralData source table p kind vals order position count bits items)
    (memory : source.memory = target.memory) (domain : source.memaddrs = target.memaddrs)
    (endian : source.be = target.be) (code : source.code = target.code) :
    GeneralData target table p kind vals order position count bits items := by
  refine {
    header := ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    keyLength := data.keyLength
    small := data.small
    capacity := data.capacity
    room := data.room
    binary := ?_
    covered := ?_
    orderMapped := ?_
    orderCell := ?_
    positionMapped := ?_
    positionCell := ?_
    valsMapped := ?_
    valsCell := ?_
    countMapped := ?_
    countCell := ?_
    queryFits := data.queryFits
    queryMapped := ?_
    slots := ?_
    little := ?_
    hashCode := ?_
    copyCode := ?_ }
  · rw [← domain]; exact data.header.mapped
  · rw [← memory]; exact data.header.capacity
  · rw [← memory]; exact data.header.keyLength
  · rw [← memory]; exact data.header.stride
  · rw [← memory]; exact data.header.keys
  · rw [← memory]; exact data.header.used
  · intro i inside
    rw [← Find.usedByte_of_fields source target p _ memory domain endian]
    exact data.binary i inside
  · intro i inside occupied
    apply data.covered i inside
    rw [Find.usedByte_of_fields source target p _ memory domain endian]
    exact occupied
  · rw [← domain]; exact data.orderMapped
  · rw [← memory]; exact data.orderCell
  · rw [← domain]; exact data.positionMapped
  · rw [← memory]; exact data.positionCell
  · rw [← domain]; exact data.valsMapped
  · rw [← memory]; exact data.valsCell
  · rw [← domain]; exact data.countMapped
  · rw [← memory]; exact data.countCell
  · rw [← domain]; exact data.queryMapped
  · rw [← domain]; exact data.slots
  · rw [← endian]; exact data.little
  · rw [← code]; exact data.hashCode
  · rw [← code]; exact data.copyCode

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.GeneralData.of_fields
