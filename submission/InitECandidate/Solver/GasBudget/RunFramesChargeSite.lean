import InitECandidate.Solver.GasBudget.RunFramesCaughtDispatch
import InitECandidate.Solver.GasBudget.RunFramesSuffixFinish
import InitECandidate.Solver.GasBudget.DispatchChargeNormal
import InitECandidate.Solver.GasBudget.DispatchChargeException
import InitECandidate.Solver.GasBudget.FrameExceptionHandler
import InitECandidate.Solver.GasBudget.ChargeEvent

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def TerminalPrefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame cont : BitVec 64) (ceiling : Nat) : Prop :=
  ∃ paid, paid ≤ ceiling ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
    emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := post.clock} ∧
    regularBudget post.memory frame = regularBudget source.memory frame ∧ post.memory (cont + 32#64) = .word 1#64 ∧
    post.memaddrs (cont + 32#64) ∧ post.globals.lookup (ofString "cur_cont") = some (.val (.word cont))

def SuffixFinish (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : OpcodeChargeSites.Kind)
    (ready : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ProgramSuffixFinish source post kind.suffix ready

theorem terminal_after_prefix (source exceptionPost post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (view : FrameException.View source) (err : BitVec 64) (paid ceiling : Nat)
    (installed : Input.OriginalCode.Installed source.code)
    (effect : StackPop.PrefixEffect source exceptionPost view.frame paid)
    (normal : evaluateHOLFiniteState (bind {exceptionPost with locals := source.locals} "err" err) opcodeHandler = (none, post))
    (bounded : paid + (2 + FrameException.choicePrice err) ≤ ceiling) :
    TerminalPrefix source post view.frame view.continuation ceiling := by
  obtain ⟨fits, small, clock, fields, budget, done⟩ := FrameException.handler_after_prefix source exceptionPost source post view err paid installed effect normal
  have domain := congrArg PanSemStateFiniteExact.memaddrs fields
  change post.memaddrs = source.memaddrs at domain
  have globals := congrArg PanSemStateFiniteExact.globals fields
  change post.globals = source.globals at globals
  refine ⟨paid + (2 + FrameException.choicePrice err), bounded, fits, clock, fields, budget, done, ?_, ?_⟩
  · rw [domain]; exact view.continuationMapped
  · rw [globals]; exact view.curCont

/-- A genuine normal caught opcode call at any of the59 sites either
terminates the current frame through the real handler, or exposes a real
positive first-charge event and the actual normal/exceptional original suffix.
The terminal path includes all caller clocks and costs at most popCount+6. -/
theorem caught_charge_site (kind : OpcodeChargeSites.Kind)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (view : FrameException.View source) (sp used op : BitVec 64)
    (arguments : List (ExpHOL 64)) (selected : OpcodeDispatch.tree.choose op = .invoke kind.label arguments)
    (read : eval source opcodeArgument = some (.val (.word op)))
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (spMapped : source.memaddrs (view.frame + 16#64)) (spCell : source.memory (view.frame + 16#64) = .word sp)
    (usedCell : source.memory (view.frame + 184#64) = .word used)
    (normal : evaluateHOLFiniteState source caughtDispatch = (none, post)) :
    TerminalPrefix source post view.frame view.continuation (kind.names.length + 6) ∨
    ∃ ready, ChargeEvent source ready view.frame (kind.names.length + 3) kind.fee ∧ SuffixFinish source post kind ready := by
  obtain ⟨positive, actualOp, callee, byteBound, actualRead, binding, cases⟩ := caught_dispatch_cases source post installed shapes normal
  have opEq : actualOp = op := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualRead.symm.trans read)))
  rw [opEq] at binding
  let entry := callEntryStateHOLFinite source callee
  have before := StackPop.PrefixEffect.call_entry source callee view.frame positive
  rcases cases with returned | caught
  · obtain ⟨target, bodyRun, postEq⟩ := returned
    obtain ⟨zero, ready, inner, returned, fits, clock, fields, restRun, scopeEq, budget, credit, progress, depth, outside⟩ :=
      OpcodeDispatch.charge_site_normal kind entry target view.frame op arguments selected binding installed view.ev view.cap _ bodyRun
    have currentFields : emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {entry with memory := ready.memory, clock := ready.clock} := by
      rw [clock]
      exact fields
    have event : ChargeEvent entry ready view.frame (kind.names.length + 2) kind.fee :=
      ⟨fits, clock, currentFields, budget, credit, OpcodeChargeSites.fee_positive_nat kind, outside⟩
    have total := event.prepend before
    have paid : 1 + (kind.names.length + 2) = kind.names.length + 3 := by omega
    rw [paid] at total
    refine Or.inr ⟨ready, total, Or.inl ⟨inner, returned, restRun, ?_⟩⟩
    rw [postEq]
    exact scopeEq
  · obtain ⟨target, err, bodyRun, handlerRun⟩ := caught
    rcases OpcodeDispatch.charge_site_exception kind entry target view.frame sp view.gas used op arguments selected binding installed shapes view.ev
        spMapped spCell (view.refillMapped 64 (by decide)) (view.haltMapped 184 (by decide)) view.gasCell usedCell view.cap
        (ofString "EvmErr") (.val (.word err)) bodyRun with underflow | insufficient | charged
    · obtain ⟨actualId, actualPayload, depth, effect, zeroCell⟩ := underflow
      have errEq : err = 2#64 := HolWordLab.word.inj (ValueHOL.val.inj actualPayload)
      rw [errEq] at handlerRun
      have total := before.trans effect
      have paid : 1 + (sp.toNat + 2) = sp.toNat + 3 := by omega
      rw [paid] at total
      apply Or.inl
      apply terminal_after_prefix source target post view 2#64 (sp.toNat + 3) (kind.names.length + 6) installed total handlerRun
      have price : FrameException.choicePrice 2#64 = 1 := by decide
      rw [price]
      omega
    · obtain ⟨actualId, actualPayload, depth, unavailable, effect⟩ := insufficient
      have errEq : err = 4#64 := HolWordLab.word.inj (ValueHOL.val.inj actualPayload)
      rw [errEq] at handlerRun
      have total := before.trans effect
      have paid : 1 + (kind.names.length + 2) = kind.names.length + 3 := by omega
      rw [paid] at total
      apply Or.inl
      apply terminal_after_prefix source target post view 4#64 (kind.names.length + 3) (kind.names.length + 6) installed total handlerRun
      have price : FrameException.choicePrice 4#64 = 1 := by decide
      rw [price]
    · obtain ⟨ready, inner, remaining, effect, progress, restRun, scopeEq⟩ := charged
      have event := (ChargeEvent.of_effect kind effect).prepend before
      have paid : 1 + (kind.names.length + 1 + 1) = kind.names.length + 3 := by omega
      rw [paid] at event
      exact Or.inr ⟨ready, event, Or.inr ⟨inner, target, err, restRun, scopeEq, handlerRun⟩⟩

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.terminal_after_prefix
#print axioms InitECandidate.Solver.GasBudget.RunFrames.caught_charge_site
