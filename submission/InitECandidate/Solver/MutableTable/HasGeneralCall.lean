import InitECandidate.Solver.MutableTable.HasEnvironment
import InitECandidate.Solver.MutableTable.HasGeneralExecution

namespace InitECandidate.Solver.MutableTable.Has
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Real original indexed-key membership caller with full scopes and
caller overhead; all nonlocal state is unchanged. -/
theorem general_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (kind : KeyHash.Kind) (cells : Find.HeaderData source table p)
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
    (hasCode : source.code.lookup (ofString "htab_has") = some (formals, body, .one))
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some [.val (.word table), .val (.word p.key)])
    (little : source.be = false)
    (enough : Find.generalProbePrice kind * order.length + (KeyHash.hashPrice kind + 2) ≤ source.clock) :
    ∃ paid answer, paid ≤ Find.generalProbePrice kind * order.length + (KeyHash.hashPrice kind + 2) ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_has") expressions continuation) =
        (let output := evaluateHOLFiniteState (bind {source with clock := source.clock - paid} name answer) continuation
         (output.1, restore source name output.2)) := by
  obtain ⟨callee, called, tLocal, keyLocal⟩ := environment source.code.lookup table p.key hasCode
  let entry := callEntryStateHOLFinite source callee
  have entryCells := Find.HeaderData.with_locals source entry table p cells rfl rfl tLocal keyLocal
  obtain ⟨paid, answer, target, bound, binaryAnswer, run, frame⟩ := general_has entry table p kind entryCells keyLength bits small capacity order room
    binary covered fits mapped queryFits queryMapped hashCode memeqCode findCode little
    (by change Find.generalProbePrice kind * order.length + (KeyHash.hashPrice kind + 1) ≤ source.clock - 1; omega)
  have callerFrame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - 1 - paid} := frame
  have actual := Input.CallNormal.pure_return_execute source target name (ofString "htab_has") expressions _ body continuation callee answer paid args called (by omega) run callerFrame
  have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
  exact ⟨paid + 1, answer, by omega, binaryAnswer, by simpa only [subtract] using actual⟩

end InitECandidate.Solver.MutableTable.Has

#print axioms InitECandidate.Solver.MutableTable.Has.general_call
