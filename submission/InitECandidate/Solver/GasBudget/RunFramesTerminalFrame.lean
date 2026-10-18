import InitECandidate.Solver.GasBudget.RunFramesActiveCharge

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real bounded terminal body with the actual frame/continuation globals
and any original immediate-completion guard, including STOP's running0. -/
def TerminalFrame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame cont : BitVec 64) (ceiling : Nat) : Prop :=
  ∃ paid, paid ≤ ceiling ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
    emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := post.clock} ∧
    regularBudget post.memory frame = regularBudget source.memory frame ∧
    post.globals.lookup (ofString "ev") = some (.val (.word frame)) ∧
    post.globals.lookup (ofString "cur_cont") = some (.val (.word cont)) ∧ ImmediateDone post frame cont

theorem TerminalFrame.of_prefix {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {frame cont : BitVec 64} {ceiling : Nat}
    (terminal : TerminalPrefix source post frame cont ceiling)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame))) : TerminalFrame source post frame cont ceiling := by
  obtain ⟨paid, bound, fits, clock, fields, budget, done, mapped, continuation⟩ := terminal
  have globals := congrArg PanSemStateFiniteExact.globals fields
  change post.globals = source.globals at globals
  exact ⟨paid, bound, fits, clock, fields, budget, by rw [globals]; exact ev, continuation, .marked 1#64 mapped done (by decide)⟩

theorem TerminalFrame.of_scopes {source phase endpoint post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame cont : BitVec 64} {ceiling : Nat}
    (terminal : TerminalFrame phase endpoint frame cont ceiling)
    (start : emptyLocalsHOLFinite phase = emptyLocalsHOLFinite source)
    (finish : emptyLocalsHOLFinite post = emptyLocalsHOLFinite endpoint) : TerminalFrame source post frame cont ceiling := by
  obtain ⟨paid, bound, fits, clock, fields, budget, ev, continuation, done⟩ := terminal
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
  refine ⟨paid, bound, ?_, ?_, ?_, ?_, ?_, ?_, done.of_fields targetMemory domain⟩
  · rw [← sourceClock]; exact fits
  · rw [targetClock, clock, sourceClock]
  · rw [targetMemory, targetClock]
    exact finish.trans (fields.trans lift)
  · rw [targetMemory, ← sourceMemory]; exact budget
  · rw [globals]; exact ev
  · rw [globals]; exact continuation

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.TerminalFrame.of_prefix
#print axioms InitECandidate.Solver.GasBudget.RunFrames.TerminalFrame.of_scopes
