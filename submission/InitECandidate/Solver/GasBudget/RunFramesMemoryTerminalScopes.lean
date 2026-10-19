import InitECandidate.Solver.GasBudget.RunFramesMemoryTerminal

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem MemoryTerminal.of_scopes {source phase endpoint post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame cont base scratch oldLength oldCapacity length capacity pointer : BitVec 64} {ceiling : Nat}
    (terminal : MemoryTerminal phase endpoint frame cont base scratch oldLength oldCapacity length capacity pointer ceiling)
    (start : emptyLocalsHOLFinite phase = emptyLocalsHOLFinite source)
    (finish : emptyLocalsHOLFinite post = emptyLocalsHOLFinite endpoint) :
    MemoryTerminal source post frame cont base scratch oldLength oldCapacity length capacity pointer ceiling := by
  obtain ⟨paid, funded, clock, view, budget, used, cost, marked, mapped, continuation, amortized, outside⟩ := terminal
  have sourceClock := congrArg PanSemStateFiniteExact.clock start
  have sourceMemory := congrArg PanSemStateFiniteExact.memory start
  have targetClock := congrArg PanSemStateFiniteExact.clock finish
  have targetMemory := congrArg PanSemStateFiniteExact.memory finish
  have domain := congrArg PanSemStateFiniteExact.memaddrs finish
  have globals := congrArg PanSemStateFiniteExact.globals finish
  change phase.clock = source.clock at sourceClock
  change phase.memory = source.memory at sourceMemory
  change post.clock = endpoint.clock at targetClock
  change post.memory = endpoint.memory at targetMemory
  change post.memaddrs = endpoint.memaddrs at domain
  change post.globals = endpoint.globals at globals
  have erased : Input.LocalEffects.erase post = Input.LocalEffects.erase endpoint := by
    have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with clock := 0}) finish
    exact same
  refine ⟨paid, ?_, ?_, view.after_erase erased, ?_, ?_, ?_, ?_, ?_, ?_, amortized, ?_⟩
  · rw [← sourceClock]; exact funded
  · rw [targetClock, clock, sourceClock]
  · rw [targetMemory, ← sourceMemory]; exact budget
  · rw [targetMemory, ← sourceMemory]; exact used
  · rw [targetMemory]; exact cost
  · rw [targetMemory]; exact marked
  · rw [domain]; exact mapped
  · rw [globals]; exact continuation
  · intro query owned apart notCont
    rw [targetMemory, ← sourceMemory]
    exact outside query owned apart notCont

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.MemoryTerminal.of_scopes
