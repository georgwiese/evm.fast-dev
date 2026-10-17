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
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [localVar "t", localVar "key"] = some [.val (.word table), .val (.word p.key)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, cells.tableLocal, cells.keyLocal]
  obtain ⟨paid, index, bound, indexBound, callRun, selected⟩ := Find.general_call source table p kind ⟨cells.mapped, cells.capacity, cells.keyLength, cells.stride, cells.keys, cells.used⟩ keyLength bits small capacity order room
    binary covered fits mapped queryFits queryMapped hashCode memeqCode findCode "i" [localVar "t", localVar "key"] afterIndex args little enough
  let entered := bind {source with clock := source.clock - paid} "i" index
  have tEntered : entered.locals.lookup (ofString "t") = some (.val (.word table)) :=
    (bind_lookup_other _ "i" "t" _ (by decide)).trans cells.tableLocal
  obtain ⟨flag, value, binaryFlag, tailRun⟩ := sized_tail entered table vals index p.capacity tEntered
    (bind_lookup_same _ _ _) (cells.mapped 16 (by simp)) cells.capacity valsMapped valsCell values indexBound
  change evaluateHOLFiniteState source (.decCall (ofString "i") .one (ofString "htab_find_slot") [localVar "t", localVar "key"] afterIndex) =
    (let result := evaluateHOLFiniteState entered afterIndex; (result.1, restore source "i" result.2)) at callRun
  rw [tailRun] at callRun
  refine ⟨paid, flag, value, restore source "i" (emptyLocalsHOLFinite entered), bound, binaryFlag, ?_, rfl⟩
  rw [body_shape]
  exact callRun

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.general_get
