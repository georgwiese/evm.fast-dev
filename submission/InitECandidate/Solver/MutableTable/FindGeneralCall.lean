import InitECandidate.Solver.MutableTable.FindGeneralExecution
import InitECandidate.Solver.MutableTable.FindCall32
import InitECandidate.Solver.MutableTable.HeaderData

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Real scoped caller of the unchanged original key-width lookup, from physical
header and mapped byte regions, including adversarial probe collisions. -/
theorem general_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Parameters)
    (kind : KeyHash.Kind) (cells : HeaderData source table p)
    (keyLength : p.keyLength = BitVec.ofNat 64 (KeyHash.keySize kind))
    (bits : Nat) (small : bits < 64) (capacity : p.capacity = BitVec.ofNat 64 (2 ^ bits))
    (order : List Nat) (room : order.length < 2 ^ bits)
    (binary : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 0 ∨ usedByte source p (BitVec.ofNat 64 i)=some 1)
    (covered : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 1→i∈order)
    (fits : ∀ i < 2 ^ bits, (p.keys + BitVec.ofNat 64 i * p.stride).toNat + KeyHash.keySize kind < 2 ^ 64)
    (mapped : ∀ i < 2 ^ bits, ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64)
      (WitnessRadix.byteAddress (p.keys + BitVec.ofNat 64 i * p.stride) offset)))
    (queryFits : p.key.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress p.key offset)))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (WitnessRadix.Memeq32.formals, WitnessRadix.Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (formals, body, .one))
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some [.val (.word table), .val (.word p.key)])
    (little : source.be = false)
    (enough : generalProbePrice kind * order.length + (KeyHash.hashPrice kind + 1) ≤ source.clock) :
    ∃ paid value, paid ≤ generalProbePrice kind * order.length + (KeyHash.hashPrice kind + 1) ∧ value.toNat ≤ p.capacity.toNat ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_find_slot") expressions continuation) =
        (let output := evaluateHOLFiniteState (bind {source with clock := source.clock - paid} name value) continuation
         (output.1, restore source name output.2)) ∧ Selection source p value := by
  obtain ⟨callee, called, tLocal, keyLocal⟩ := environment source.code.lookup table p.key findCode
  let entry := callEntryStateHOLFinite source callee
  have entryCells := HeaderData.with_locals source entry table p cells rfl rfl tLocal keyLocal
  obtain ⟨paid, value, bound, valueBound, result, frame, selected⟩ := general_find entry table p kind entryCells keyLength bits small capacity order room
    binary covered fits mapped queryFits queryMapped hashCode memeqCode little
    (by change generalProbePrice kind * order.length + (KeyHash.hashPrice kind) ≤ source.clock - 1; omega)
  let post := (evaluateHOLFiniteState entry body).2
  have run : evaluateHOLFiniteState entry body = (some (.returned (.val (.word value))), post) := Prod.ext result rfl
  have callerFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - 1 - paid} := frame
  have actual := Input.CallNormal.pure_return_execute source post name (ofString "htab_find_slot") expressions _ body continuation callee value paid args called (by omega) run callerFrame
  have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
  exact ⟨paid + 1, value, by omega, valueBound, by simpa only [subtract] using actual, Selection.of_fields entry source p value rfl rfl rfl selected⟩

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.general_call
