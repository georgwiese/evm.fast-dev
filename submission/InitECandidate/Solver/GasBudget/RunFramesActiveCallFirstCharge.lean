import InitECandidate.Solver.GasBudget.RunFramesCallFirstCharge
import InitECandidate.Solver.GasBudget.RunFramesActiveBody

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout MemoryWriter Input.RlpWrite

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
theorem active_call_first_charge (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (view : FrameException.View source)
    (base current capacity pointer scratch running pc length sp used : BitVec 64)
    (memoryView : MemoryExtend.View source view.frame base current capacity pointer scratch)
    (aligned : view.frame.toNat % 8 = 0) (queryMapped : BytesMapped source (view.frame + 240#64) 20)
    (plan : Plan) (slots : List Nat) (cursor floor : Nat) (table : TableState source .account plan slots cursor floor)
    (environment : WarmKeys.Environment source) (separate : view.frame.toNat + 280 ≤ floor)
    (tableMapped : source.memaddrs (view.frame + 168#64)) (tableCell : source.memory (view.frame + 168#64) = .word (cell plan .header 0))
    (reservoirAway : BytesAway (view.frame + 240#64) (view.message + 48#64) 20)
    (header : ActiveHeader source view.frame view.continuation running pc length)
    (read : eval (bind (activeEntry source pc) "err" 0#64) opcodeArgument = some (.val (.word 241#64)))
    (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (spMapped : source.memaddrs (view.frame + 16#64)) (spCell : source.memory (view.frame + 16#64) = .word sp)
    (usedCell : source.memory (view.frame + 184#64) = .word used)
    (normal : evaluateHOLFiniteState source loopBody = (none, post)) :
    FrameTerminal source post view.frame view.continuation (8 * slots.length + 70) ∨
    ∃ (value inStart inSize outStart outSize : U256Value.Words) (warm : BitVec 64) (paid : Nat)
      (ready : PanSemStateFiniteExact 64 Guest.HostMemory), paid ≤ 8 * slots.length + 67 ∧
      FrameChargeEvent source ready view.frame paid
        (CallFirstFee.amount warm (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1 value).toNat ∧
      (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1.toNat + (CallGas.stipend value).toNat + 100 ≤
        (CallFirstFee.amount warm (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1 value).toNat ∧
      Input.ExecutionTail ready CallOpcode.afterFee none post ∧
      CallOpcode.ChargedLocals ready view.frame view.message current value inStart inSize outStart outSize warm := by
  obtain ⟨handled, caughtRun, postScope⟩ := active_caught_normal source post view.frame view.continuation running pc length header normal
  let phase := bind (activeEntry source pc) "err" 0#64
  have setup : StackPop.PrefixEffect source phase view.frame 0 := (StackPop.PrefixEffect.refl source view.frame).of_emptyLocals rfl
  let currentView := view.after_prefix setup
  have currentMemoryView : MemoryExtend.View phase view.frame base current capacity pointer scratch := memoryView.after_erase rfl
  have currentTable : TableState phase .account plan slots cursor floor := table.of_fields rfl rfl rfl rfl
  have currentEnvironment : WarmKeys.Environment phase := environment.of_fields rfl rfl rfl
  rcases caught_call_first_charge phase handled currentView base current capacity pointer scratch sp used currentMemoryView aligned queryMapped
      plan slots cursor floor currentTable currentEnvironment separate tableMapped tableCell reservoirAway read shapes spMapped spCell usedCell caughtRun with terminal | charged
  · exact Or.inl (terminal.of_scopes rfl postScope)
  · obtain ⟨value, inStart, inSize, outStart, outSize, warm, paid, ready, bound, event, surplus, tail, locals⟩ := charged
    have total := event.prepend setup.frame_effect
    simp only [Nat.zero_add] at total
    exact Or.inr ⟨value, inStart, inSize, outStart, outSize, warm, paid, ready, bound, total, surplus, .locals tail postScope, locals⟩

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.active_call_first_charge
