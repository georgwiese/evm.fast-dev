import InitECandidate.Solver.GasBudget.RunFramesTerminalFrame
import InitECandidate.Solver.GasBudget.StopNoException

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual caught STOP dispatch always takes its real normal return: the
original STOP/pc_add bodies cannot throw. It leaves the actual frame halted
with conserved regular ledger, at precisely three source caller clocks. -/
theorem caught_stop_terminal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (view : FrameException.View source)
    (running pc length : BitVec 64) (header : ActiveHeader source view.frame view.continuation running pc length)
    (read : eval source opcodeArgument = some (.val (.word 0#64)))
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (contNotPC : view.continuation + 32#64 ≠ view.frame + 0#64)
    (normal : evaluateHOLFiniteState source caughtDispatch = (none, post)) :
    TerminalFrame source post view.frame view.continuation 3 := by
  obtain ⟨positive, actualOp, callee, byteBound, actualRead, binding, cases⟩ := caught_dispatch_cases source post installed shapes normal
  have opEq : actualOp = 0#64 := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualRead.symm.trans read)))
  rw [opEq] at binding
  let entry := callEntryStateHOLFinite source callee
  rcases cases with returned | caught
  · obtain ⟨target, bodyRun, postEq⟩ := returned
    obtain ⟨fits, zero, clock, frameEq, budget, halted, usedSame, outside⟩ := OpcodeDispatch.stop_body_normal entry target view.frame binding
      (OriginalCodeEnvironment.op_stop source.code installed) view.ev (OriginalCodeEnvironment.pc_add source.code installed) _ bodyRun
    obtain ⟨ev, continuation, markedMapped, markedCell, runningMapped, runningCell, nonzero, pcMapped, pcCell, lengthMapped, lengthCell, inside⟩ := header
    have contNotRunning : view.continuation + 32#64 ≠ view.frame + 104#64 := by
      intro equal
      have words : (.word 0#64 : HolWordLab 64) = .word running := markedCell.symm.trans ((congrArg source.memory equal).trans runningCell)
      exact nonzero (HolWordLab.word.inj words).symm
    have bodyFields := congrArg emptyLocalsHOLFinite frameEq
    have fields : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := post.clock} := by
      rw [postEq]
      change emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := target.memory, clock := target.clock}
      rw [clock]
      exact bodyFields
    have globals := congrArg PanSemStateFiniteExact.globals fields
    change post.globals = source.globals at globals
    have domain := congrArg PanSemStateFiniteExact.memaddrs fields
    change post.memaddrs = source.memaddrs at domain
    have markedPost : post.memory (view.continuation + 32#64) = .word 0#64 := by
      rw [postEq]
      exact (outside _ contNotPC contNotRunning).trans markedCell
    have haltedPost : post.memory (view.frame + 104#64) = .word 0#64 := by rw [postEq]; exact halted
    have markedPostMapped : post.memaddrs (view.continuation + 32#64) := by rw [domain]; exact markedMapped
    have runningPostMapped : post.memaddrs (view.frame + 104#64) := by rw [domain]; exact runningMapped
    refine ⟨3, Nat.le_refl _, ?_, ?_, fields, ?_, ?_, ?_, .halted markedPostMapped markedPost runningPostMapped haltedPost⟩
    · change 2 ≤ source.clock - 1 at fits
      omega
    · rw [postEq]
      change target.clock = _
      rw [clock]
      change source.clock - 1 - 2 = source.clock - 3
      omega
    · rw [postEq]; exact budget
    · rw [globals]; exact view.ev
    · rw [globals]; exact view.curCont
  · obtain ⟨target, err, bodyRun, handlerRun⟩ := caught
    exact False.elim (OpcodeDispatch.stop_no_exception entry installed binding _ _ (congrArg Prod.fst bodyRun))

theorem active_stop_terminal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (view : FrameException.View source)
    (running pc length : BitVec 64) (header : ActiveHeader source view.frame view.continuation running pc length)
    (read : eval (bind (activeEntry source pc) "err" 0#64) opcodeArgument = some (.val (.word 0#64)))
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (contNotPC : view.continuation + 32#64 ≠ view.frame + 0#64)
    (normal : evaluateHOLFiniteState source loopBody = (none, post)) : TerminalFrame source post view.frame view.continuation 3 := by
  obtain ⟨handled, caughtRun, postScope⟩ := active_caught_normal source post view.frame view.continuation running pc length header normal
  let phase := bind (activeEntry source pc) "err" 0#64
  have setup : StackPop.PrefixEffect source phase view.frame 0 := (StackPop.PrefixEffect.refl source view.frame).of_emptyLocals rfl
  let current := view.after_prefix setup
  have terminal := caught_stop_terminal phase handled current running pc length header read installed shapes contNotPC caughtRun
  exact terminal.of_scopes rfl postScope

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.caught_stop_terminal
#print axioms InitECandidate.Solver.GasBudget.RunFrames.active_stop_terminal
