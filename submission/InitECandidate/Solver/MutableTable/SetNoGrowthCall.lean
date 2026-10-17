import InitECandidate.Solver.MutableTable.SetNoGrowthExecution

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- Real ignored-result original setter caller when the actual count guard
excludes growth. Exact memory/control/clock frame and physical counter change
are derived, for all original widths and arbitrary collisions/alignment. -/
theorem no_growth_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (kind : KeyHash.Kind) (vals order position count value : BitVec 64) (bits : Nat) (items : List Nat)
    (data : Insert.GeneralData source table p kind vals order position count bits items)
    (countBound : count.toNat ≤ items.length) (room : 2 * items.length + 2 ≤ 2 ^ bits)
    (memeqCode : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (setCode : source.code.lookup (ofString "htab_set") = some (TableCall.formals, body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (TableCall.values table p.key value))
    (enough : noGrowthPrice kind items.length + 1 ≤ source.clock) :
    ∃ paid memory, paid ≤ noGrowthPrice kind items.length + 1 ∧
      evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_set") arguments) =
        (none, {source with memory := memory, clock := source.clock - paid}) ∧
      (memory (table + 24#64) = .word count ∨ memory (table + 24#64) = .word (count + 1#64)) := by
  obtain ⟨callee, called, tLocal, keyLocal, valueLocal⟩ := TableCall.environment source.code.lookup (ofString "htab_set") body table p.key value setCode
  let entry := callEntryStateHOLFinite source callee
  have entryData := Insert.GeneralData.of_fields source entry table p kind vals order position count bits items data rfl rfl rfl rfl
  obtain ⟨paid, memory, target, bound, run, frame, counter⟩ := no_growth_execute entry table p kind vals order position count value bits items
    entryData tLocal keyLocal valueLocal countBound room memeqCode findCode insertCode (by change noGrowthPrice kind items.length ≤ source.clock - 1; omega)
  have callerFrame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - 1 - paid} := frame
  have actual := ignored_memory_call source target (ofString "htab_set") .one arguments (TableCall.values table p.key value) body callee
    (.val (.word 0#64)) paid memory args called (by omega) run (by simp [shapeEqHOL, shapeOfHOLExact]) callerFrame
  have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
  exact ⟨paid + 1, memory, by omega, by simpa only [subtract] using actual, counter⟩

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.no_growth_call
