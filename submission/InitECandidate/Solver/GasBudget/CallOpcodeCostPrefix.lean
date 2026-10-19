import InitECandidate.Solver.GasBudget.CallOpcodeCostProgram

namespace InitECandidate.Solver.GasBudget.CallOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem cost_prefix_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch message query : BitVec 64)
    (value inStart inSize outStart outSize : U256Value.Words)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (messageMapped : source.memaddrs (frame + 112#64)) (messageCell : source.memory (frame + 112#64) = .word message)
    (valueCell : source.locals.lookup (ofString "value") = some (U256Value.tuple value))
    (inStartCell : source.locals.lookup (ofString "in_start") = some (U256Value.tuple inStart))
    (inSizeCell : source.locals.lookup (ofString "in_size") = some (U256Value.tuple inSize))
    (outStartCell : source.locals.lookup (ofString "out_start") = some (U256Value.tuple outStart))
    (outSizeCell : source.locals.lookup (ofString "out_size") = some (U256Value.tuple outSize))
    (queryCell : source.locals.lookup (ofString "to") = some (.val (.word query)))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source afterPops = (some (.returned returned), post)) :
    ∃ paid ready inner, paid ≤ 44 ∧ paid ≤ source.clock ∧ ready.clock = source.clock - paid ∧
      Input.LocalEffects.erase ready = Input.LocalEffects.erase source ∧
      MemoryExtend.View ready frame base current capacity pointer scratch ∧
      ready.locals.lookup (ofString "vz") = some (.val (.word (U256Zero.resultWord value))) ∧
      ready.locals.lookup (ofString "x") = some (MemoryExpansionCost.pairValue (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current)) ∧
      ready.locals.lookup (ofString "to") = some (.val (.word query)) ∧
      evaluateHOLFiniteState ready afterCost = (some (.returned returned), inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock := by
  have messageRead := frame_read source frame 112#64 message view.ev messageMapped messageCell
  rw [message_shape] at run
  obtain ⟨messagePost, messageRun, messageScope⟩ := Input.declaration_return_word source post "msg" (frameLoad 112#64) message afterMessage returned messageRead run
  let entered := bind source "msg" message
  have entryOther (key : String) (different : ofString "msg" ≠ ofString key) : entered.locals.lookup (ofString key) = source.locals.lookup (ofString key) := bind_lookup_other _ _ _ _ different
  have valueRead : eval entered (localVar "value") = some (U256Value.tuple value) := by
    simp [eval, localVar, evalHOLExact, toExact, (entryOther "value" (by decide)).trans valueCell]
  rw [zero_shape] at messageRun
  obtain ⟨zeroPaid, first, firstPost, zeroPositive, zeroBound, zeroFits, firstEq, firstFields, guardRun, zeroScope⟩ :=
    MemoryCostCalls.normal .zero entered messagePost "vz" (localVar "value") afterZero value returned view.installed valueRead messageRun
  have firstVZ := Input.KnownUnaryPrefix.lookup_same firstEq
  have firstOther (key : String) (different : ofString "vz" ≠ ofString key) := Input.KnownUnaryPrefix.lookup_other firstEq key different
  rw [guard_shape] at guardRun
  have costRun := static_pure.normal_continue first firstPost costProgram returned guardRun
  have args : evalListHOLFinite first (h := fun query => Classical.propDecidable (first.memaddrs query))
      [localVar "in_start", localVar "in_size", localVar "out_start", localVar "out_size"] =
      some [U256Value.tuple inStart, U256Value.tuple inSize, U256Value.tuple outStart, U256Value.tuple outSize] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar,
      (firstOther "in_start" (by decide)).trans ((entryOther "in_start" (by decide)).trans inStartCell),
      (firstOther "in_size" (by decide)).trans ((entryOther "in_size" (by decide)).trans inSizeCell),
      (firstOther "out_start" (by decide)).trans ((entryOther "out_start" (by decide)).trans outStartCell),
      (firstOther "out_size" (by decide)).trans ((entryOther "out_size" (by decide)).trans outSizeCell)]
  have costView : MemoryExpansionCost.View first frame current :=
    (show MemoryExpansionCost.View entered frame current from ⟨view.installed, view.ev, view.mapped 32 (by simp), view.lengthCell⟩).after_erase firstFields
  rw [cost_shape] at costRun
  obtain ⟨costPaid, ready, inner, costPositive, costBound, costFits, readyEq, readyFields, tailRun, costScope⟩ :=
    MemoryExpansionCost2.normal_prefix first firstPost frame current inStart inSize outStart outSize costView "x"
      [localVar "in_start", localVar "in_size", localVar "out_start", localVar "out_size"] afterCost returned args costRun
  have finalFields : Input.LocalEffects.erase ready = Input.LocalEffects.erase source := readyFields.trans firstFields
  have firstClock : first.clock = source.clock - zeroPaid := by rw [firstEq]; rfl
  have clock : ready.clock = source.clock - (zeroPaid + costPaid) := by rw [readyEq]; change first.clock - costPaid = _; rw [firstClock]; omega
  refine ⟨zeroPaid + costPaid, ready, inner, by change zeroPaid ≤ 1 at zeroBound; omega, ?_, clock, finalFields,
    view.after_erase finalFields, ?_, Input.KnownUnaryPrefix.lookup_same readyEq, ?_, tailRun, ?_, ?_⟩
  · rw [firstClock] at costFits
    change zeroPaid ≤ source.clock at zeroFits
    omega
  · exact (Input.KnownUnaryPrefix.lookup_other readyEq "vz" (by decide)).trans firstVZ
  · exact (Input.KnownUnaryPrefix.lookup_other readyEq "to" (by decide)).trans
      ((firstOther "to" (by decide)).trans ((entryOther "to" (by decide)).trans queryCell))
  · rw [messageScope, zeroScope, costScope]; rfl
  · rw [messageScope, zeroScope, costScope]; rfl

end InitECandidate.Solver.GasBudget.CallOpcode

#print axioms InitECandidate.Solver.GasBudget.CallOpcode.cost_prefix_normal
