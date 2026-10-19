import InitECandidate.Solver.GasBudget.CallOpcodeLocals
import InitECandidate.Solver.GasBudget.CallOpcodeEntry
import InitECandidate.Solver.GasBudget.CallOpcodeCostPrefix
import InitECandidate.Solver.GasBudget.CallEntryTable
import InitECandidate.Solver.GasBudget.FrameChargeEvent

namespace InitECandidate.Solver.GasBudget.CallOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout Input.RlpWrite MemoryWriter

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
/-- A real normal original CALL body derives its first genuine charge from
the complete entry, static guard, cost2 and warmth query. There are no assumed
future helper runs, supplied charge amounts or source clock allowances. -/
theorem normal_first_charge (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch message : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (aligned : frame.toNat % 8 = 0) (queryMapped : BytesMapped source (frame + 240#64) 20)
    (plan : Plan) (slots : List Nat) (cursor floor : Nat) (table : TableState source .account plan slots cursor floor)
    (environment : WarmKeys.Environment source) (separate : frame.toNat + 280 ≤ floor)
    (messageMapped : source.memaddrs (frame + 112#64)) (messageCell : source.memory (frame + 112#64) = .word message)
    (tableMapped : source.memaddrs (frame + 168#64)) (tableCell : source.memory (frame + 168#64) = .word (cell plan .header 0))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    ∃ (value inStart inSize outStart outSize : U256Value.Words) (warm : BitVec 64) (paid : Nat)
      (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ 8 * slots.length + 65 ∧
      FrameChargeEvent source ready frame paid
        (CallFirstFee.amount warm (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1 value).toNat ∧
      (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1.toNat + (CallGas.stipend value).toNat + 100 ≤
        (CallFirstFee.amount warm (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1 value).toNat ∧
      evaluateHOLFiniteState ready afterFee = (some (.returned returned), inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock ∧
      ChargedLocals ready frame message current value inStart inSize outStart outSize warm := by
  obtain ⟨entryPaid, entry, entryPost, entryBound, entryFits, entryClock, entryView, cells, queryCell, entryBudget, entryUsed, depth, entryFields, costRun, entryScope, entryPostClock, entryOutside⟩ :=
    entry_normal source post frame base current capacity pointer scratch view aligned queryMapped returned run
  have tableEntry := preserve_table frame .account plan slots cursor floor table aligned view.frameFits separate entryFields entryOutside
  have entryGlobals := congrArg PanSemStateFiniteExact.globals entryFields
  have entryDomain := congrArg PanSemStateFiniteExact.memaddrs entryFields
  have entryEndian := congrArg PanSemStateFiniteExact.be entryFields
  have entryCode := congrArg PanSemStateFiniteExact.code entryFields
  change entry.globals = source.globals at entryGlobals
  change entry.memaddrs = source.memaddrs at entryDomain
  change entry.be = source.be at entryEndian
  change entry.code = source.code at entryCode
  have entryEnvironment : WarmKeys.Environment entry := environment.of_fields entryCode entryDomain entryEndian
  have entryMessageMapped : entry.memaddrs (frame + 112#64) := by rw [entryDomain]; exact messageMapped
  have entryMessage : entry.memory (frame + 112#64) = .word message :=
    (entryOutside _ (offsets_ne frame 112#64 16#64 (by decide)) (AddressMasked.header_away frame 112 aligned view.frameFits (by decide))).trans messageCell
  obtain ⟨value, valueCell⟩ := cells "value" (by simp [firstNames, remainingNames])
  obtain ⟨inStart, inStartCell⟩ := cells "in_start" (by simp [firstNames, remainingNames])
  obtain ⟨inSize, inSizeCell⟩ := cells "in_size" (by simp [firstNames, remainingNames])
  obtain ⟨outStart, outStartCell⟩ := cells "out_start" (by simp [firstNames, remainingNames])
  obtain ⟨outSize, outSizeCell⟩ := cells "out_size" (by simp [firstNames, remainingNames])
  obtain ⟨costPaid, costReady, costPost, costBound, costFits, costClock, costFields, costView, vzCell, xCell, queryReady, feeRun, costScope, costPostClock, costMsg, costOther⟩ :=
    cost_prefix_normal entry entryPost frame base current capacity pointer scratch message (frame + 240#64) value inStart inSize outStart outSize entryView
      entryMessageMapped entryMessage valueCell inStartCell inSizeCell outStartCell outSizeCell queryCell returned costRun
  have costMemory := Input.LocalEffects.memory_of_erase entry costReady costFields
  have costGlobals := congrArg PanSemStateFiniteExact.globals costFields
  have costDomain := congrArg PanSemStateFiniteExact.memaddrs costFields
  have costEndian := congrArg PanSemStateFiniteExact.be costFields
  have costCode := congrArg PanSemStateFiniteExact.code costFields
  change costReady.globals = entry.globals at costGlobals
  change costReady.memaddrs = entry.memaddrs at costDomain
  change costReady.be = entry.be at costEndian
  change costReady.code = entry.code at costCode
  have costTable : TableState costReady .account plan slots cursor floor := tableEntry.of_fields costGlobals costMemory costDomain costEndian
  have costEnvironment : WarmKeys.Environment costReady := entryEnvironment.of_fields costCode costDomain costEndian
  have costTableMapped : costReady.memaddrs (frame + 168#64) := by rw [costDomain, entryDomain]; exact tableMapped
  have costTableCell : costReady.memory (frame + 168#64) = .word (cell plan .header 0) := by
    rw [costMemory]
    exact (entryOutside _ (offsets_ne frame 168#64 16#64 (by decide)) (AddressMasked.header_away frame 168 aligned view.frameFits (by decide))).trans tableCell
  have currentCap : regularBudget costReady.memory frame ≤ 16777216 := by rw [costMemory, entryBudget]; exact cap
  have queryFits : (frame + 240#64).toNat + 20 < 2^64 := by
    have number : (frame + 240#64).toNat = frame.toNat + 240 := BitVec.toNat_add_of_lt (by change frame.toNat + 240 < 2^64; have bound := view.frameFits; omega)
    have bound := view.frameFits
    omega
  have currentMapped : ∀ offset < 20, costReady.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress (frame + 240#64) offset)) := by
    intro offset inside
    rw [costDomain, entryDomain]
    exact queryMapped offset inside
  have args : evalListHOLFinite costReady (h := fun query => Classical.propDecidable (costReady.memaddrs query)) [localVar "to"] = some [.val (.word (frame + 240#64))] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, queryReady]
  rw [first_fee_shape] at feeRun
  obtain ⟨warm, feePaid, ready, inner, feeBound, event, surplus, tailRun, feeScope, feePostClock, warmCell, feeOther⟩ :=
    CallFirstFee.normal costReady costPost frame (frame + 240#64) _ _ value plan slots cursor floor costTable costEnvironment costView.installed costView.ev
      costTableMapped costTableCell queryFits currentMapped vzCell xCell currentCap [localVar "to"] afterFee returned args feeRun
  have unchanged := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with clock := costReady.clock}) costFields
  change emptyLocalsHOLFinite costReady = emptyLocalsHOLFinite {entry with clock := costReady.clock} at unchanged
  rw [costClock] at unchanged
  have effect := StackPop.PrefixEffect.unchanged entry costReady frame costPaid costFits costClock unchanged
  have fromEntry := event.prepend effect
  have fromSource := fromEntry.prepend_frame entryFits entryClock entryFields entryBudget entryUsed entryOutside
  have feeErase := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with clock := 0}) feeScope
  change Input.LocalEffects.erase costPost = Input.LocalEffects.erase inner at feeErase
  rw [CallFirstFee.price_exact] at feeBound
  refine ⟨value, inStart, inSize, outStart, outSize, warm, entryPaid + (costPaid + feePaid), ready, inner, by omega,
    fromSource, surplus, tailRun, entryScope.trans (costScope.trans feeErase), entryPostClock.trans (costPostClock.trans feePostClock),
    charged_locals_of_preservation entry costReady ready frame message current value inStart inSize outStart outSize warm
      valueCell inStartCell inSizeCell outStartCell outSizeCell
      (cells "gasv" (by simp [firstNames, remainingNames])) (cells "tov" (by simp [firstNames, remainingNames]))
      xCell vzCell queryReady costMsg costOther warmCell feeOther⟩

end InitECandidate.Solver.GasBudget.CallOpcode

#print axioms InitECandidate.Solver.GasBudget.CallOpcode.normal_first_charge
