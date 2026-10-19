import InitECandidate.Solver.GasBudget.CallOpcodeEntryException
import InitECandidate.Solver.GasBudget.CallOpcodeCostException
import InitECandidate.Solver.GasBudget.CallFirstFeeException
import InitECandidate.Solver.GasBudget.FrameChargeEvent

namespace InitECandidate.Solver.GasBudget.CallOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout Input.RlpWrite MemoryWriter

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
theorem exception_first_charge (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch message sp gas used : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (aligned : frame.toNat % 8 = 0) (queryMapped : BytesMapped source (frame + 240#64) 20)
    (plan : Plan) (slots : List Nat) (cursor floor : Nat) (table : TableState source .account plan slots cursor floor)
    (environment : WarmKeys.Environment source) (separate : frame.toNat + 280 ≤ floor)
    (messageMapped : source.memaddrs (frame + 112#64)) (messageCell : source.memory (frame + 112#64) = .word message)
    (tableMapped : source.memaddrs (frame + 168#64)) (tableCell : source.memory (frame + 168#64) = .word (cell plan .header 0))
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (shape : source.eshapes.lookup (ofString "EvmErr") = some .one) (cap : regularBudget source.memory frame ≤ 16777216)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) :
    (identifier = ofString "EvmErr" ∧ (payload = .val (.word 2#64) ∨ payload = .val (.word 8#64) ∨ payload = .val (.word 4#64)) ∧
      ∃ paid, paid ≤ 8 * slots.length + 65 ∧ FramePrefixEffect source post frame paid) ∨
    ∃ (value inStart inSize outStart outSize : U256Value.Words) (warm : BitVec 64) (paid : Nat)
      (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory), paid ≤ 8 * slots.length + 65 ∧
      FrameChargeEvent source ready frame paid
        (CallFirstFee.amount warm (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1 value).toNat ∧
      (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1.toNat + (CallGas.stipend value).toNat + 100 ≤
        (CallFirstFee.amount warm (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1 value).toNat ∧
      evaluateHOLFiniteState ready afterFee = (some (.exception identifier payload), inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock := by
  rcases entry_exception source post frame base current capacity pointer scratch sp view aligned queryMapped spMapped spCell shape identifier payload run with failed | continued
  · obtain ⟨actualId, actualPayload, paid, bound, effect⟩ := failed
    exact Or.inl ⟨actualId, Or.inl actualPayload, paid, by omega, effect⟩
  · obtain ⟨entryPaid, entry, entryPost, remaining, entryBound, entryEffect, entrySP, depth, cells, queryCell, costRun, entryScope⟩ := continued
    have entryView := entryEffect.buffer_view view aligned
    have entryMessageMapped : entry.memaddrs (frame + 112#64) := by rw [entryEffect.memaddrs_eq]; exact messageMapped
    have entryMessage : entry.memory (frame + 112#64) = .word message :=
      (entryEffect.outside _ (offsets_ne frame 112#64 16#64 (by decide)) (AddressMasked.header_away frame 112 aligned view.frameFits (by decide))).trans messageCell
    obtain ⟨value, valueCell⟩ := cells "value" (by simp [firstNames, remainingNames])
    obtain ⟨inStart, inStartCell⟩ := cells "in_start" (by simp [firstNames, remainingNames])
    obtain ⟨inSize, inSizeCell⟩ := cells "in_size" (by simp [firstNames, remainingNames])
    obtain ⟨outStart, outStartCell⟩ := cells "out_start" (by simp [firstNames, remainingNames])
    obtain ⟨outSize, outSizeCell⟩ := cells "out_size" (by simp [firstNames, remainingNames])
    rcases cost_prefix_exception entry entryPost frame base current capacity pointer scratch message (frame + 240#64) value inStart inSize outStart outSize entryView
        entryMessageMapped entryMessage valueCell inStartCell inSizeCell outStartCell outSizeCell queryCell identifier payload costRun with failed | continued
    · obtain ⟨actualId, actualPayload, costEffect⟩ := failed
      exact Or.inl ⟨actualId, Or.inr (Or.inl actualPayload), entryPaid + 1, by omega,
        (entryEffect.trans costEffect.frame_effect).of_emptyLocals entryScope⟩
    · obtain ⟨costPaid, costReady, costPost, costBound, costFits, costClock, costFields, vzCell, xCell, queryReady, feeRun, costScope⟩ := continued
      have unchanged := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with clock := costReady.clock}) costFields
      change emptyLocalsHOLFinite costReady = emptyLocalsHOLFinite {entry with clock := costReady.clock} at unchanged
      rw [costClock] at unchanged
      have costEffect := StackPop.PrefixEffect.unchanged entry costReady frame costPaid costFits costClock unchanged
      have before := entryEffect.trans costEffect.frame_effect
      have costView := before.buffer_view view aligned
      have costTable := preserve_table frame .account plan slots cursor floor table aligned view.frameFits separate before.fields before.outside
      have endian := congrArg PanSemStateFiniteExact.be before.fields
      change costReady.be = source.be at endian
      have costEnvironment : WarmKeys.Environment costReady := environment.of_fields before.code_eq before.memaddrs_eq endian
      have currentTableMapped : costReady.memaddrs (frame + 168#64) := by rw [before.memaddrs_eq]; exact tableMapped
      have currentTableCell : costReady.memory (frame + 168#64) = .word (cell plan .header 0) :=
        (before.outside _ (offsets_ne frame 168#64 16#64 (by decide)) (AddressMasked.header_away frame 168 aligned view.frameFits (by decide))).trans tableCell
      have currentGasMapped : costReady.memaddrs (frame + 64#64) := by rw [before.memaddrs_eq]; exact gasMapped
      have currentUsedMapped : costReady.memaddrs (frame + 184#64) := by rw [before.memaddrs_eq]; exact usedMapped
      have currentGas : costReady.memory (frame + 64#64) = .word gas :=
        (before.outside _ (offsets_ne frame 64#64 16#64 (by decide)) (AddressMasked.header_away frame 64 aligned view.frameFits (by decide))).trans gasCell
      have currentUsed : costReady.memory (frame + 184#64) = .word used := before.used.trans usedCell
      have currentCap : regularBudget costReady.memory frame ≤ 16777216 := by rw [before.budget]; exact cap
      have currentShape : costReady.eshapes.lookup (ofString "EvmErr") = some .one := by rw [before.eshapes_eq]; exact shape
      have queryFits : (frame + 240#64).toNat + 20 < 2^64 := by
        have number : (frame + 240#64).toNat = frame.toNat + 240 := BitVec.toNat_add_of_lt (by change frame.toNat + 240 < 2^64; have bound := view.frameFits; omega)
        have bound := view.frameFits
        omega
      have currentMapped : ∀ offset < 20, costReady.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress (frame + 240#64) offset)) := by
        intro offset inside
        rw [before.memaddrs_eq]
        exact queryMapped offset inside
      have args : evalListHOLFinite costReady (h := fun query => Classical.propDecidable (costReady.memaddrs query)) [localVar "to"] = some [.val (.word (frame + 240#64))] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, queryReady]
      rw [first_fee_shape] at feeRun
      rcases CallFirstFee.exception_prefix costReady costPost frame (frame + 240#64) _ _ gas used value plan slots cursor floor costTable costEnvironment costView.installed costView.ev
          currentTableMapped currentTableCell queryFits currentMapped vzCell xCell currentGasMapped currentUsedMapped currentGas currentUsed currentCap currentShape
          [localVar "to"] afterFee identifier payload args feeRun with failed | charged
      · obtain ⟨actualId, actualPayload, feePaid, feeBound, failedEffect⟩ := failed
        exact Or.inl ⟨actualId, Or.inr (Or.inr actualPayload), entryPaid + costPaid + feePaid, by omega,
          (before.trans failedEffect.frame_effect).of_emptyLocals (entryScope.trans costScope)⟩
      · obtain ⟨warm, feePaid, ready, inner, feeBound, event, surplus, tailRun, feeScope, feeClock⟩ := charged
        have fullEvent := event.prepend_frame before.fits before.clock before.fields before.budget before.used before.outside
        have scopes := entryScope.trans costScope
        have erased := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with clock := 0}) scopes
        change Input.LocalEffects.erase post = Input.LocalEffects.erase costPost at erased
        have clock := congrArg PanSemStateFiniteExact.clock scopes
        change post.clock = costPost.clock at clock
        exact Or.inr ⟨value, inStart, inSize, outStart, outSize, warm, entryPaid + costPaid + feePaid, ready, inner, by omega,
          fullEvent, surplus, tailRun, erased.trans feeScope, clock.trans feeClock⟩

end InitECandidate.Solver.GasBudget.CallOpcode

#print axioms InitECandidate.Solver.GasBudget.CallOpcode.exception_first_charge
