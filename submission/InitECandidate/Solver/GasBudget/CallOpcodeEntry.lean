import InitECandidate.Solver.GasBudget.CallOpcodeProgram

namespace InitECandidate.Solver.GasBudget.CallOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite MemoryWriter

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
/-- The real interleaved CALL entry: two actual pops, masked-address writes,
then five more actual pops. All seven real quads, the formatted query, stack
depth and current buffer/ledger follow from the original body execution. -/
theorem entry_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (aligned : frame.toNat % 8 = 0) (queryMapped : BytesMapped source (frame + 240#64) 20)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    ∃ paid ready inner, paid ≤ 15 ∧ paid ≤ source.clock ∧ ready.clock = source.clock - paid ∧
      MemoryExtend.View ready frame base current capacity pointer scratch ∧
      (∀ name ∈ firstNames ++ remainingNames, ∃ words : U256Value.Words, ready.locals.lookup (ofString name) = some (U256Value.tuple words)) ∧
      ready.locals.lookup (ofString "to") = some (.val (.word (frame + 240#64))) ∧
      regularBudget ready.memory frame = regularBudget source.memory frame ∧
      ready.memory (frame + 184#64) = source.memory (frame + 184#64) ∧
      (wordAt ready.memory (frame + 16#64)).toNat + 7 = (wordAt source.memory (frame + 16#64)).toNat ∧
      emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := ready.clock} ∧
      evaluateHOLFiniteState ready afterPops = (some (.returned returned), inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock ∧
      (∀ query, query ≠ frame + 16#64 → BytesAway (frame + 240#64) query 20 → ready.memory query = source.memory query) := by
  rw [body_shape] at normal
  obtain ⟨popped, firstPost, firstEffect, firstCells, firstOther, addressRun, firstFields, firstClock, firstDepth⟩ :=
    StackPop.pops_typed_normal firstNames source post frame (by decide) addressProgram
      (OriginalCodeEnvironment.stack_pop source.code view.installed) view.ev returned normal
  obtain ⟨destination, destinationCell⟩ := firstCells "tov" (by simp [firstNames])
  have args : evalListHOLFinite popped (h := fun query => Classical.propDecidable (popped.memaddrs query)) [localVar "tov"] = some [U256Value.tuple destination] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, destinationCell]
  have poppedOriginal : Input.OriginalCode.Installed popped.code := by rw [firstEffect.code_eq]; exact view.installed
  have poppedEV : popped.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [firstEffect.globals_eq]; exact view.ev
  have poppedMapped : BytesMapped popped (frame + 240#64) 20 := by
    intro offset inside
    rw [firstEffect.memaddrs_eq]
    exact queryMapped offset inside
  obtain ⟨addressPaid, memory, addressPost, addressBound, addressFits, restRun, addressScope, addressAway⟩ :=
    AddressMasked.call_normal popped firstPost frame destination poppedOriginal poppedEV poppedMapped "to" [localVar "tov"] afterAddress returned args addressRun
  let addressed := bind {popped with memory := memory, clock := popped.clock - addressPaid} "to" (frame + 240#64)
  have addressBuffer := (view.after_pops firstEffect).after_address_masked memory "to" addressPaid aligned addressAway
  obtain ⟨ready, inner, restEffect, restCells, restOther, tailRun, restFields, restClock, restDepth⟩ :=
    StackPop.pops_typed_normal remainingNames addressed addressPost frame (by decide) afterPops
      (OriginalCodeEnvironment.stack_pop addressed.code addressBuffer.installed) addressBuffer.ev returned restRun
  obtain ⟨addressBudget, addressUsed⟩ := AddressMasked.budget_preserved popped.memory memory frame aligned view.frameFits addressAway
  have addressSP : (wordAt addressed.memory (frame + 16#64)).toNat = (wordAt popped.memory (frame + 16#64)).toNat := by
    have same := addressAway _ (AddressMasked.header_away frame 16 aligned view.frameFits (by decide))
    change (wordAt memory (frame + 16#64)).toNat = (wordAt popped.memory (frame + 16#64)).toNat
    simp only [wordAt, same]
  have firstFit := firstEffect.fits
  have startClock := firstEffect.clock
  change 2 ≤ source.clock at firstFit
  change popped.clock = source.clock - 2 at startClock
  have restFits := restEffect.fits
  have endpointClock := restEffect.clock
  change 5 ≤ popped.clock - addressPaid at restFits
  change ready.clock = popped.clock - addressPaid - 5 at endpointClock
  have firstLift := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    emptyLocalsHOLFinite {state with memory := ready.memory, clock := ready.clock}) firstEffect.fields
  have totalFields : emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := ready.clock} := restEffect.fields.trans firstLift
  refine ⟨2 + addressPaid + 5, ready, inner, by omega, by omega, by rw [endpointClock, startClock]; omega,
    addressBuffer.after_pops restEffect, ?_, ?_, ?_, ?_, ?_, totalFields, tailRun, ?_, ?_, ?_⟩
  · intro name member
    rcases List.mem_append.mp member with old | new
    · obtain ⟨words, cell⟩ := firstCells name old
      have nameChoices : name = "gasv" ∨ name = "tov" := by simpa [firstNames] using old
      have notTo : ofString "to" ≠ ofString name := by rcases nameChoices with rfl | rfl <;> decide
      have earlier : addressed.locals.lookup (ofString name) = some (U256Value.tuple words) :=
        (bind_lookup_other _ _ _ _ notTo).trans cell
      exact ⟨words, (restOther name (remaining_away name (by rcases nameChoices with rfl | rfl <;> simp))).trans earlier⟩
    · exact restCells name new
  · exact (restOther "to" (remaining_away "to" (by simp))).trans (bind_lookup_same _ _ _)
  · exact restEffect.budget.trans (addressBudget.trans firstEffect.budget)
  · exact restEffect.used.trans (addressUsed.trans firstEffect.used)
  · change (wordAt ready.memory (frame + 16#64)).toNat + 5 = (wordAt addressed.memory (frame + 16#64)).toNat at restDepth
    change (wordAt popped.memory (frame + 16#64)).toNat + 2 = (wordAt source.memory (frame + 16#64)).toNat at firstDepth
    rw [addressSP] at restDepth
    omega
  · rw [addressScope] at firstFields
    exact firstFields.trans restFields
  · rw [addressScope] at firstClock
    exact firstClock.trans restClock
  · intro query notSP away
    exact (restEffect.outside query notSP).trans ((addressAway query away).trans (firstEffect.outside query notSP))

end InitECandidate.Solver.GasBudget.CallOpcode

#print axioms InitECandidate.Solver.GasBudget.CallOpcode.entry_normal
