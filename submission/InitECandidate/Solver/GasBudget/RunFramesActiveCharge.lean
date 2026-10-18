import InitECandidate.Solver.GasBudget.RunFramesChargeSite
import InitECandidate.Solver.GasBudget.RunFramesActiveBody
import InitECandidate.Solver.GasBudget.RunFramesDone

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem TerminalPrefix.of_scopes {source phase endpoint post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame cont : BitVec 64} {ceiling : Nat}
    (terminal : TerminalPrefix phase endpoint frame cont ceiling)
    (start : emptyLocalsHOLFinite phase = emptyLocalsHOLFinite source)
    (finish : emptyLocalsHOLFinite post = emptyLocalsHOLFinite endpoint) :
    TerminalPrefix source post frame cont ceiling := by
  obtain ⟨paid, bound, fits, clock, fields, budget, done, mapped, continuation⟩ := terminal
  have sourceClock := congrArg PanSemStateFiniteExact.clock start
  change phase.clock = source.clock at sourceClock
  have sourceMemory := congrArg PanSemStateFiniteExact.memory start
  change phase.memory = source.memory at sourceMemory
  have targetClock := congrArg PanSemStateFiniteExact.clock finish
  change post.clock = endpoint.clock at targetClock
  have targetMemory := congrArg PanSemStateFiniteExact.memory finish
  change post.memory = endpoint.memory at targetMemory
  have domain := congrArg PanSemStateFiniteExact.memaddrs finish
  change post.memaddrs = endpoint.memaddrs at domain
  have globals := congrArg PanSemStateFiniteExact.globals finish
  change post.globals = endpoint.globals at globals
  have lift := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    emptyLocalsHOLFinite {state with memory := endpoint.memory, clock := endpoint.clock}) start
  refine ⟨paid, bound, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← sourceClock]; exact fits
  · rw [targetClock, clock, sourceClock]
  · rw [targetMemory, targetClock]
    exact finish.trans (fields.trans lift)
  · rw [targetMemory, ← sourceMemory]; exact budget
  · rw [targetMemory]; exact done
  · rw [domain]; exact mapped
  · rw [globals]; exact continuation

theorem TerminalPrefix.immediate_done {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {frame cont : BitVec 64} {ceiling : Nat}
    (terminal : TerminalPrefix source post frame cont ceiling) : ImmediateDone post frame cont := by
  obtain ⟨paid, bound, fits, clock, fields, budget, done, mapped, continuation⟩ := terminal
  exact .marked 1#64 mapped done (by decide)

/-- Retain the genuine caller locals and handler endpoint through the
zero-clock lexical scopes of the complete original active loop body. -/
def ScopedSuffixFinish (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : OpcodeChargeSites.Kind)
    (ready : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ScopedProgramSuffixFinish source post kind.suffix ready

/-- Whole actual active loop-body gas-or-terminal classification at all59
original sites. Underflow/out-of-gas completes the real handler; every other
normal body exposes its genuinely reached positive charge and original suffix.
No future opcode/handler execution, model, argument success or funding is supplied. -/
theorem active_charge_site (kind : OpcodeChargeSites.Kind)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (view : FrameException.View source)
    (running pc length sp used op : BitVec 64) (arguments : List (ExpHOL 64))
    (header : ActiveHeader source view.frame view.continuation running pc length)
    (selected : OpcodeDispatch.tree.choose op = .invoke kind.label arguments)
    (read : eval (bind (activeEntry source pc) "err" 0#64) opcodeArgument = some (.val (.word op)))
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (spMapped : source.memaddrs (view.frame + 16#64)) (spCell : source.memory (view.frame + 16#64) = .word sp)
    (usedCell : source.memory (view.frame + 184#64) = .word used)
    (normal : evaluateHOLFiniteState source loopBody = (none, post)) :
    TerminalPrefix source post view.frame view.continuation (kind.names.length + 6) ∨
    ∃ ready, ChargeEvent source ready view.frame (kind.names.length + 3) kind.fee ∧ ScopedSuffixFinish source post kind ready := by
  obtain ⟨handled, caughtRun, postScope⟩ := active_caught_normal source post view.frame view.continuation running pc length header normal
  let phase := bind (activeEntry source pc) "err" 0#64
  have setup : StackPop.PrefixEffect source phase view.frame 0 := (StackPop.PrefixEffect.refl source view.frame).of_emptyLocals rfl
  let current := view.after_prefix setup
  rcases caught_charge_site kind phase handled current sp used op arguments selected read installed shapes spMapped spCell usedCell caughtRun with terminal | charged
  · exact Or.inl (terminal.of_scopes rfl postScope)
  · obtain ⟨ready, event, finish⟩ := charged
    have total := event.prepend setup
    simp only [Nat.zero_add] at total
    exact Or.inr ⟨ready, total, phase, handled, rfl, postScope, finish⟩

theorem site_pop_count_bound (kind : OpcodeChargeSites.Kind) : kind.names.length ≤ 3 := by
  cases kind <;> decide

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.TerminalPrefix.of_scopes
#print axioms InitECandidate.Solver.GasBudget.RunFrames.TerminalPrefix.immediate_done
#print axioms InitECandidate.Solver.GasBudget.RunFrames.active_charge_site
#print axioms InitECandidate.Solver.GasBudget.RunFrames.site_pop_count_bound
