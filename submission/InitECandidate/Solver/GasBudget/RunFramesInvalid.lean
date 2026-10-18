import InitECandidate.Solver.GasBudget.RunFramesActiveCharge

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real invalid-opcode branch throws original EvmErr5 and completes
the real frame handler. Its entire caught-call path spends four source clocks. -/
theorem caught_invalid_terminal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (view : FrameException.View source)
    (op : BitVec 64) (selected : OpcodeDispatch.tree.choose op = .failed)
    (read : eval source opcodeArgument = some (.val (.word op)))
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (normal : evaluateHOLFiniteState source caughtDispatch = (none, post)) :
    TerminalPrefix source post view.frame view.continuation 4 := by
  obtain ⟨positive, actualOp, callee, byteBound, actualRead, binding, cases⟩ := caught_dispatch_cases source post installed shapes normal
  have opEq : actualOp = op := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualRead.symm.trans read)))
  rw [opEq] at binding
  let entry := callEntryStateHOLFinite source callee
  have before := StackPop.PrefixEffect.call_entry source callee view.frame positive
  rcases cases with returned | caught
  · obtain ⟨target, bodyRun, postEq⟩ := returned
    obtain ⟨zero, function, arguments, middle, picked, helperRun, scopeEq⟩ := OpcodeDispatch.normal_helper entry target op binding _ bodyRun
    rw [selected] at picked
    cases picked
  · obtain ⟨target, err, bodyRun, handlerRun⟩ := caught
    rw [OpcodeDispatch.body_choice entry op binding, selected, OpcodeDispatch.Action.program] at bodyRun
    have shape : entry.eshapes.lookup (ofString "EvmErr") = some .one := shapes Input.OriginalExceptions.Kind.EvmErr
    have raised : evaluateHOLFiniteState entry (.raise (ofString "EvmErr") (.const 5#64)) =
        (some (.exception (ofString "EvmErr") (.val (.word 5#64))), emptyLocalsHOLFinite entry) := by
      simp [evaluateHOLFiniteState_raise, shape, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    have same := bodyRun.symm.trans raised
    have tagged := PanSemResultExact.exception.inj (Option.some.inj (congrArg Prod.fst same))
    have errEq : err = 5#64 := HolWordLab.word.inj (ValueHOL.val.inj tagged.2)
    have targetEq := congrArg Prod.snd same
    change target = emptyLocalsHOLFinite entry at targetEq
    have scope : emptyLocalsHOLFinite target = emptyLocalsHOLFinite entry := by rw [targetEq]; rfl
    have effect := before.of_emptyLocals scope
    rw [errEq] at handlerRun
    exact terminal_after_prefix source target post view 5#64 1 4 installed effect handlerRun (by decide)

theorem active_invalid_terminal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (view : FrameException.View source)
    (running pc length op : BitVec 64) (header : ActiveHeader source view.frame view.continuation running pc length)
    (selected : OpcodeDispatch.tree.choose op = .failed)
    (read : eval (bind (activeEntry source pc) "err" 0#64) opcodeArgument = some (.val (.word op)))
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (normal : evaluateHOLFiniteState source loopBody = (none, post)) :
    TerminalPrefix source post view.frame view.continuation 4 := by
  obtain ⟨handled, caughtRun, postScope⟩ := active_caught_normal source post view.frame view.continuation running pc length header normal
  let phase := bind (activeEntry source pc) "err" 0#64
  have setup : StackPop.PrefixEffect source phase view.frame 0 := (StackPop.PrefixEffect.refl source view.frame).of_emptyLocals rfl
  let current := view.after_prefix setup
  have terminal := caught_invalid_terminal phase handled current op selected read installed shapes caughtRun
  exact terminal.of_scopes rfl postScope

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.caught_invalid_terminal
#print axioms InitECandidate.Solver.GasBudget.RunFrames.active_invalid_terminal
