import InitECandidate.Solver.GasBudget.CallOpcodeProgram
import InitECandidate.Solver.GasBudget.StackPopsTypedException
import InitECandidate.Solver.GasBudget.AddressMaskedExceptionPrefix
import InitECandidate.Solver.GasBudget.FramePrefixEffect

namespace InitECandidate.Solver.GasBudget.CallOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite MemoryWriter

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem entry_exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch sp : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (aligned : frame.toNat % 8 = 0) (queryMapped : BytesMapped source (frame + 240#64) 20)
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (shape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) :
    (identifier = ofString "EvmErr" ∧ payload = .val (.word 2#64) ∧ ∃ paid, paid ≤ 15 ∧ FramePrefixEffect source post frame paid) ∨
    ∃ paid ready inner remaining, paid ≤ 15 ∧ FramePrefixEffect source ready frame paid ∧
      ready.memory (frame + 16#64) = .word remaining ∧ remaining.toNat + 7 = sp.toNat ∧
      (∀ name ∈ firstNames ++ remainingNames, ∃ words : U256Value.Words, ready.locals.lookup (ofString name) = some (U256Value.tuple words)) ∧
      ready.locals.lookup (ofString "to") = some (.val (.word (frame + 240#64))) ∧
      evaluateHOLFiniteState ready afterPops = (some (.exception identifier payload), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  rw [body_shape] at run
  rcases StackPop.pops_typed_exception firstNames source post frame sp (by decide) addressProgram
      (OriginalCodeEnvironment.stack_pop source.code view.installed) view.ev spMapped spCell shape identifier payload run with failed | continued
  · obtain ⟨actualId, actualPayload, bound, effect, zero⟩ := failed
    exact Or.inl ⟨actualId, actualPayload, sp.toNat + 1, by change sp.toNat + 1 ≤ 2 at bound; omega, effect.frame_effect⟩
  · obtain ⟨popped, firstPost, firstRemaining, firstEffect, firstSP, firstDepth, firstCells, firstOther, addressRun, firstScope⟩ := continued
    obtain ⟨destination, destinationCell⟩ := firstCells "tov" (by simp [firstNames])
    have args : evalListHOLFinite popped (h := fun query => Classical.propDecidable (popped.memaddrs query)) [localVar "tov"] = some [U256Value.tuple destination] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, destinationCell]
    have poppedView := view.after_pops firstEffect
    have poppedMapped : BytesMapped popped (frame + 240#64) 20 := by
      intro offset inside
      rw [firstEffect.memaddrs_eq]
      exact queryMapped offset inside
    obtain ⟨addressPaid, memory, addressPost, addressBound, addressFits, restRun, addressScope, addressAway⟩ :=
      AddressMasked.exception_prefix popped firstPost frame destination poppedView.installed poppedView.ev poppedMapped "to" [localVar "tov"] afterAddress identifier payload args addressRun
    let addressed := bind {popped with memory := memory, clock := popped.clock - addressPaid} "to" (frame + 240#64)
    have addressEffect := FramePrefixEffect.masked popped memory frame "to" addressPaid addressFits aligned view.frameFits addressAway
    have before := firstEffect.frame_effect.trans addressEffect
    have addressView := before.buffer_view view aligned
    have addressSP : addressed.memory (frame + 16#64) = .word firstRemaining :=
      (addressAway _ (AddressMasked.header_away frame 16 aligned view.frameFits (by decide))).trans firstSP
    have addressMapped : addressed.memaddrs (frame + 16#64) := by rw [before.memaddrs_eq]; exact spMapped
    have addressShape : addressed.eshapes.lookup (ofString "EvmErr") = some .one := by rw [before.eshapes_eq]; exact shape
    have original : addressed.code.lookup (ofString "stack_pop") = some ([], StackPop.body, StackPop.shape) := OriginalCodeEnvironment.stack_pop addressed.code addressView.installed
    rcases StackPop.pops_typed_exception remainingNames addressed addressPost frame firstRemaining (by decide) afterPops
        original addressView.ev addressMapped addressSP addressShape identifier payload restRun with failed | completed
    · obtain ⟨actualId, actualPayload, bound, effect, zero⟩ := failed
      have combined := before.trans effect.frame_effect
      have scopes : emptyLocalsHOLFinite post = emptyLocalsHOLFinite addressPost := by rw [addressScope] at firstScope; exact firstScope
      refine Or.inl ⟨actualId, actualPayload, firstNames.length + addressPaid + (firstRemaining.toNat + 1), ?_, combined.of_emptyLocals scopes⟩
      change firstRemaining.toNat + 1 ≤ 5 at bound
      change 2 + addressPaid + (firstRemaining.toNat + 1) ≤ 15
      omega
    · obtain ⟨ready, inner, remaining, restEffect, readySP, restDepth, restCells, restOther, tailRun, restScope⟩ := completed
      have combined := before.trans restEffect.frame_effect
      refine Or.inr ⟨firstNames.length + addressPaid + remainingNames.length, ready, inner, remaining,
        by change 2 + addressPaid + 5 ≤ 15; omega, combined, readySP, ?_, ?_, ?_, tailRun, ?_⟩
      · change firstRemaining.toNat + 2 = sp.toNat at firstDepth
        change remaining.toNat + 5 = firstRemaining.toNat at restDepth
        omega
      · intro name member
        rcases List.mem_append.mp member with old | new
        · obtain ⟨words, cell⟩ := firstCells name old
          have nameChoices : name = "gasv" ∨ name = "tov" := by simpa [firstNames] using old
          have notTo : ofString "to" ≠ ofString name := by rcases nameChoices with rfl | rfl <;> decide
          have earlier : addressed.locals.lookup (ofString name) = some (U256Value.tuple words) := (bind_lookup_other _ _ _ _ notTo).trans cell
          exact ⟨words, (restOther name (remaining_away name (by rcases nameChoices with rfl | rfl <;> simp))).trans earlier⟩
        · exact restCells name new
      · exact (restOther "to" (remaining_away "to" (by simp))).trans (bind_lookup_same _ _ _)
      · rw [addressScope] at firstScope
        exact firstScope.trans restScope

end InitECandidate.Solver.GasBudget.CallOpcode

#print axioms InitECandidate.Solver.GasBudget.CallOpcode.entry_exception
