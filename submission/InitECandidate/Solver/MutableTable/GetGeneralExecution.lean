import InitECandidate.Solver.MutableTable.GetGeneralOrigin
import InitECandidate.Solver.MutableTable.FindGeneralCall
import InitECandidate.Solver.MutableTable.GetSizedTail

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete original indexed-key retrieval. All actual hash/comparison/
probe and value reads are derived from physical mapped regions; typed table
values and entry/occupancy/room conditions remain explicit. -/
theorem general_get (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (kind : KeyHash.Kind) (cells : Find.HeaderCells source table p)
    (keyLength : p.keyLength = BitVec.ofNat 64 (KeyHash.keySize kind))
    (bits : Nat) (small : bits < 64) (capacity : p.capacity = BitVec.ofNat 64 (2 ^ bits))
    (order : List Nat) (room : order.length < 2 ^ bits)
    (binary : ∀ i<2^bits,Find.usedByte source p (BitVec.ofNat 64 i)=some 0 ∨ Find.usedByte source p (BitVec.ofNat 64 i)=some 1)
    (covered : ∀ i<2^bits,Find.usedByte source p (BitVec.ofNat 64 i)=some 1→i∈order)
    (fits : ∀ i < 2 ^ bits, (p.keys + BitVec.ofNat 64 i * p.stride).toNat + KeyHash.keySize kind < 2 ^ 64)
    (mapped : ∀ i < 2 ^ bits, ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64)
      (WitnessRadix.byteAddress (p.keys + BitVec.ofNat 64 i * p.stride) offset)))
    (queryFits : p.key.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress p.key offset)))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (WitnessRadix.Memeq32.formals, WitnessRadix.Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (vals : BitVec 64) (valsMapped : source.memaddrs (table + 40#64))
    (valsCell : source.memory (table + 40#64) = .word vals)
    (values : ∀ slot : BitVec 64, slot.toNat < p.capacity.toNat →
      ∃ value, source.memaddrs (vals + slot * 8#64) ∧ source.memory (vals + slot * 8#64) = .word value)
    (little : source.be = false)
    (enough : Find.generalProbePrice kind * order.length + (KeyHash.hashPrice kind + 1) ≤ source.clock) :
    ∃ paid flag value target, paid ≤ Find.generalProbePrice kind * order.length + (KeyHash.hashPrice kind + 1) ∧ (flag = 0#64 ∨ flag = 1#64) ∧
      evaluateHOLFiniteState source body = (some (.returned (pair flag value)), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - paid} := by
  obtain ⟨paid,flag,value,target,price,binaryFlag,origin,run,frame⟩ := general_get_origin source table p kind cells keyLength bits small capacity order room binary covered fits mapped
    queryFits queryMapped hashCode memeqCode findCode vals valsMapped valsCell values little enough
  exact ⟨paid,flag,value,target,price,binaryFlag,run,frame⟩

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.general_get
