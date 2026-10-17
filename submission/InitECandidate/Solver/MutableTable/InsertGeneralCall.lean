import InitECandidate.Solver.MutableTable.InsertGeneralExecution
import InitECandidate.Solver.MutableTable.TableCallEnvironment

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- The last original count store wins, even independently of earlier cell
contents. This is the physical counter used by later growth/truncation. -/
theorem general_result_count (memory : WordWrites.Memory) (be : Bool) (width : Nat) (p : Find.Parameters)
    (table vals order position index count value : BitVec 64) :
    generalResultMemory memory be width p table vals order position index count value (table + 24#64) = .word (count + 1#64) := by
  simp [generalResultMemory, suffixMemory, countWrites, WordWrites.write, StoreWord.put]

/-- Real ignored-result raw-insertion caller for every original key width.
All entry locals come from the actual ABI. The final memory is exact and the
physical item-count increment is derived; all other nonlocal fields frame. -/
theorem general_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (kind : KeyHash.Kind) (vals order position count value : BitVec 64) (bits : Nat) (items : List Nat)
    (data : GeneralData source table p kind vals order position count bits items)
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (TableCall.values table p.key value))
    (enough : items.length + KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 2 ≤ source.clock) :
    ∃ paid index, paid ≤ items.length + KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 2 ∧
      index.toNat < p.capacity.toNat ∧
      evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_insert_raw") arguments) =
        (none, {source with
          memory := (generalResultMemory source.memory source.be (KeyHash.keySize kind) p table vals order position index count value)
          clock := source.clock - paid}) ∧
      generalResultMemory source.memory source.be (KeyHash.keySize kind) p table vals order position index count value (table + 24#64) = .word (count + 1#64) ∧ Find.usedByte source p index = some 0 := by
  obtain ⟨callee, called, tLocal, keyLocal, valueLocal⟩ := TableCall.environment source.code.lookup (ofString "htab_insert_raw") body table p.key value insertCode
  let entry := callEntryStateHOLFinite source callee
  have entryData := GeneralData.of_fields source entry table p kind vals order position count bits items data rfl rfl rfl rfl
  obtain ⟨paid, index, target, bound, inside, run, frame, empty⟩ := general_execute entry table p kind vals order position count value bits items
    entryData tLocal keyLocal valueLocal (by change items.length + KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ≤ source.clock - 1; omega)
  let memory := generalResultMemory source.memory source.be (KeyHash.keySize kind) p table vals order position index count value
  have callerFrame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - 1 - paid} := frame
  have actual := ignored_memory_call source target (ofString "htab_insert_raw") .one arguments (TableCall.values table p.key value) body callee
    (.val (.word 0#64)) paid memory args called (by omega) run (by simp [shapeEqHOL, shapeOfHOLExact]) callerFrame
  have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
  exact ⟨paid + 1, index, by omega, inside, by simpa only [subtract] using actual,
    general_result_count source.memory source.be (KeyHash.keySize kind) p table vals order position index count value, empty⟩

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.general_result_count
#print axioms InitECandidate.Solver.MutableTable.Insert.general_call
