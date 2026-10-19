import InitECandidate.Solver.GasBudget.CallOpcodeCostProgram
import InitECandidate.Solver.GasBudget.MemoryExpansionCost2ExceptionPrefix
import InitECandidate.Solver.GasBudget.U256ZeroExceptionPrefix
import InitECandidate.Solver.Input.ExceptionWordDeclaration
import InitECandidate.Solver.Input.LiteralGuardException
import InitECandidate.Solver.Input.ExceptionControl

namespace InitECandidate.Solver.GasBudget.CallOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

set_option maxRecDepth 10000 in
theorem static_form : ∃ test, staticGuard = .ite test (.raise (ofString "EvmErr") (.const 8#64)) .skip := by
  simp only [staticGuard, afterZero, afterMessage, afterPops, body, Guest.guestFn_op_call, OpcodeChargeSites.stripPops,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, Option.map_some]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem cost_prefix_exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
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
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source afterPops = (some (.exception identifier payload), post)) :
    (identifier = ofString "EvmErr" ∧ payload = .val (.word 8#64) ∧ StackPop.PrefixEffect source post frame 1) ∨
    ∃ paid ready inner, paid ≤ 44 ∧ paid ≤ source.clock ∧ ready.clock = source.clock - paid ∧
      Input.LocalEffects.erase ready = Input.LocalEffects.erase source ∧
      ready.locals.lookup (ofString "vz") = some (.val (.word (U256Zero.resultWord value))) ∧
      ready.locals.lookup (ofString "x") = some (MemoryExpansionCost.pairValue (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current)) ∧
      ready.locals.lookup (ofString "to") = some (.val (.word query)) ∧
      evaluateHOLFiniteState ready afterCost = (some (.exception identifier payload), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner ∧
      ready.locals.lookup (ofString "msg") = some (.val (.word message)) ∧
      (∀ key : String, ofString "x" ≠ ofString key → ofString "vz" ≠ ofString key → ofString "msg" ≠ ofString key →
        ready.locals.lookup (ofString key) = source.locals.lookup (ofString key)) := by
  have messageRead := frame_read source frame 112#64 message view.ev messageMapped messageCell
  rw [message_shape] at run
  obtain ⟨messagePost, messageRun, messageScope⟩ := Input.declaration_exception_word source post "msg" (frameLoad 112#64) message afterMessage identifier payload messageRead run
  let entered := bind source "msg" message
  have entryOther (key : String) (different : ofString "msg" ≠ ofString key) : entered.locals.lookup (ofString key) = source.locals.lookup (ofString key) := bind_lookup_other _ _ _ _ different
  have valueRead : eval entered (localVar "value") = some (U256Value.tuple value) := by
    simp [eval, localVar, evalHOLExact, toExact, (entryOther "value" (by decide)).trans valueCell]
  rw [zero_shape] at messageRun
  obtain ⟨zeroPaid, first, firstPost, zeroPositive, zeroBound, zeroFits, firstEq, firstFields, guardRun, zeroScope⟩ :=
    U256Zero.exception_prefix entered messagePost view.installed "vz" (localVar "value") afterZero value identifier payload valueRead messageRun
  have zeroEq : zeroPaid = 1 := by omega
  subst zeroPaid
  have firstVZ := Input.KnownUnaryPrefix.lookup_same firstEq
  have firstOther (key : String) (different : ofString "vz" ≠ ofString key) := Input.KnownUnaryPrefix.lookup_other firstEq key different
  have firstClock : first.clock = source.clock - 1 := by rw [firstEq]; rfl
  rw [guard_shape] at guardRun
  rcases Input.sequence_exception first firstPost staticGuard costProgram identifier payload guardRun with failed | continued
  · obtain ⟨test, form⟩ := static_form
    rw [form] at failed
    obtain ⟨actualId, actualPayload, fields, clock⟩ := Input.literal_guard_exception first firstPost test (ofString "EvmErr") identifier 8#64 payload failed
    have before : StackPop.PrefixEffect source first frame 1 := StackPop.PrefixEffect.unchanged source first frame 1 zeroFits firstClock (by rw [firstEq]; rfl)
    have scopes : emptyLocalsHOLFinite post = emptyLocalsHOLFinite first := by rw [messageScope, zeroScope]; exact fields
    exact Or.inl ⟨actualId, actualPayload, before.of_emptyLocals scopes⟩
  · obtain ⟨middle, guardPassed, costRun⟩ := continued
    have middleEq : middle = first := by
      have unchanged := (static_pure.summary first).1 (congrArg Prod.fst guardPassed)
      rw [guardPassed] at unchanged
      exact unchanged
    subst middle
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
      MemoryExpansionCost2.exception_prefix first firstPost frame current inStart inSize outStart outSize costView "x"
        [localVar "in_start", localVar "in_size", localVar "out_start", localVar "out_size"] afterCost identifier payload args costRun
    have finalFields : Input.LocalEffects.erase ready = Input.LocalEffects.erase source := readyFields.trans firstFields
    have clock : ready.clock = source.clock - (1 + costPaid) := by rw [readyEq]; change first.clock - costPaid = _; rw [firstClock]; omega
    have msgCell : ready.locals.lookup (ofString "msg") = some (.val (.word message)) :=
      (Input.KnownUnaryPrefix.lookup_other readyEq "msg" (by decide)).trans
        ((firstOther "msg" (by decide)).trans (bind_lookup_same _ _ _))
    have localsOther (key : String) (notX : ofString "x" ≠ ofString key)
        (notVZ : ofString "vz" ≠ ofString key) (notMsg : ofString "msg" ≠ ofString key) :
        ready.locals.lookup (ofString key) = source.locals.lookup (ofString key) :=
      (Input.KnownUnaryPrefix.lookup_other readyEq key notX).trans
        ((firstOther key notVZ).trans (entryOther key notMsg))
    refine Or.inr ⟨1 + costPaid, ready, inner, by omega, ?_, clock, finalFields, ?_, Input.KnownUnaryPrefix.lookup_same readyEq, ?_, tailRun, ?_, msgCell, localsOther⟩
    · rw [firstClock] at costFits
      change 1 ≤ source.clock at zeroFits
      omega
    · exact (Input.KnownUnaryPrefix.lookup_other readyEq "vz" (by decide)).trans firstVZ
    · exact (Input.KnownUnaryPrefix.lookup_other readyEq "to" (by decide)).trans
        ((firstOther "to" (by decide)).trans ((entryOther "to" (by decide)).trans queryCell))
    · rw [messageScope, zeroScope, costScope]; rfl

end InitECandidate.Solver.GasBudget.CallOpcode

#print axioms InitECandidate.Solver.GasBudget.CallOpcode.static_form
#print axioms InitECandidate.Solver.GasBudget.CallOpcode.cost_prefix_exception
