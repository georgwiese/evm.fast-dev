import InitECandidate.Solver.MutableTable.GetOtherExecution
import InitECandidate.Solver.MutableTable.GetCall32

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Real original retrieval caller, including the caller clock and pair ABI.
The query and table need no alignment or favorable-collision assumption. -/
theorem other_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (width : Nat) (smallWidth : width ≤ 64) (not20 : width ≠ 20) (not32 : width ≠ 32) (not52 : width ≠ 52) (cells : Find.HeaderData source table p)
    (keyLength : p.keyLength = BitVec.ofNat 64 (width))
    (bits : Nat) (small : bits < 64) (capacity : p.capacity = BitVec.ofNat 64 (2 ^ bits))
    (order : List Nat) (room : order.length < 2 ^ bits)
    (binary : ∀ i<2^bits,Find.usedByte source p (BitVec.ofNat 64 i)=some 0 ∨ Find.usedByte source p (BitVec.ofNat 64 i)=some 1)
    (covered : ∀ i<2^bits,Find.usedByte source p (BitVec.ofNat 64 i)=some 1→i∈order)
    (fits : ∀ i < 2 ^ bits, (p.keys + BitVec.ofNat 64 i * p.stride).toNat + width < 2 ^ 64)
    (mapped : ∀ i < 2 ^ bits, ∀ offset < width, source.memaddrs (panByteAlignHOL (width := 64)
      (WitnessRadix.byteAddress (p.keys + BitVec.ofNat 64 i * p.stride) offset)))
    (queryFits : p.key.toNat + width < 2 ^ 64)
    (queryMapped : ∀ offset < width, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress p.key offset)))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (WitnessRadix.Memeq32.formals, WitnessRadix.Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (vals : BitVec 64) (valsMapped : source.memaddrs (table + 40#64))
    (valsCell : source.memory (table + 40#64) = .word vals)
    (values : ∀ slot : BitVec 64, slot.toNat < p.capacity.toNat →
      ∃ value, source.memaddrs (vals + slot * 8#64) ∧ source.memory (vals + slot * 8#64) = .word value)
    (getCode : source.code.lookup (ofString "htab_get") = some (formals, body, pairShape))
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some [.val (.word table), .val (.word p.key)])
    (enough : Find.otherProbePrice width * order.length + (MemeqByteRuntime.price width + 3) ≤ source.clock) :
    ∃ paid flag value, paid ≤ Find.otherProbePrice width * order.length + (MemeqByteRuntime.price width + 3) ∧ (flag = 0#64 ∨ flag = 1#64) ∧
      evaluateHOLFiniteState source (.decCall (ofString name) pairShape (ofString "htab_get") expressions continuation) =
        (let result := evaluateHOLFiniteState (setVarHOLFinite (ofString name) (pair flag value) {source with clock := source.clock - paid}) continuation
         (result.1, restore source name result.2)) := by
  obtain ⟨callee, called, tLocal, keyLocal⟩ := environment source.code.lookup table p.key getCode
  let entry := callEntryStateHOLFinite source callee
  have entryCells := Find.HeaderData.with_locals source entry table p cells rfl rfl tLocal keyLocal
  obtain ⟨paid, flag, value, target, bound, binaryFlag, run, frame⟩ := other_get entry table p width smallWidth not20 not32 not52 entryCells keyLength bits small capacity order room
    binary covered fits mapped queryFits queryMapped hashCode memeqCode findCode vals valsMapped valsCell values
    (by change Find.otherProbePrice width * order.length + (MemeqByteRuntime.price width + 2) ≤ source.clock - 1; omega)
  have shapePass : (shapeEqHOL (shapeOfHOLExact (pair flag value)) pairShape && shapeEqHOL (shapeOfHOLExact (pair flag value)) pairShape) = true := by
    simp [pair, pairShape, shapeOfHOLExact, shapeEqHOL_eq_true]
  have callerFrame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - 1 - paid} := frame
  have actual := pure_value_call source target name (ofString "htab_get") pairShape pairShape expressions _ body continuation callee
    (pair flag value) paid args called (by omega) run shapePass callerFrame
  have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
  exact ⟨paid + 1, flag, value, by omega, binaryFlag, by simpa only [subtract] using actual⟩

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.other_call
