import InitECandidate.Solver.GasBudget.RunFramesMemoryTerminalRank
import InitECandidate.Solver.GasBudget.RunFramesMemoryTerminalScopes

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def completionWriteOffsets : List Nat := revertWriteOffsets ++ [104]

/-- Actual terminal iteration with a possibly expanded buffer. Completion
may be the continuation marker or the real running0 header. -/
def MemoryCompletion (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame cont base scratch oldLength oldCapacity length capacity pointer : BitVec 64) (ceiling : Nat) : Prop :=
  ∃ paid, paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
    MemoryExtend.View post frame base length capacity pointer scratch ∧
    regularBudget post.memory frame = regularBudget source.memory frame ∧
    (wordAt source.memory (frame + 184#64)).toNat ≤ (wordAt post.memory (frame + 184#64)).toNat ∧
    (MemoryGasCost.resultWord length).toNat ≤ (wordAt post.memory (frame + 184#64)).toNat ∧
    ImmediateDone post frame cont ∧
    post.globals.lookup (ofString "cur_cont") = some (.val (.word cont)) ∧
    paid + MemoryExtend.potential oldLength oldCapacity ≤ MemoryExtend.potential length capacity + ceiling ∧
    (∀ query, Arenas.Outside base scratch query →
      (∀ offset ∈ completionWriteOffsets, query ≠ frame + BitVec.ofNat 64 offset) →
      query ≠ cont + 32#64 → post.memory query = source.memory query)

theorem MemoryTerminal.completion {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame cont base scratch oldLength oldCapacity length capacity pointer : BitVec 64} {ceiling : Nat}
    (terminal : MemoryTerminal source post frame cont base scratch oldLength oldCapacity length capacity pointer ceiling) :
    MemoryCompletion source post frame cont base scratch oldLength oldCapacity length capacity pointer ceiling := by
  obtain ⟨paid, funded, clock, view, budget, used, cost, marked, mapped, continuation, amortized, outside⟩ := terminal
  refine ⟨paid, funded, clock, view, budget, used, cost, .marked 1#64 mapped marked (by decide), continuation, amortized, ?_⟩
  intro query owned apart notCont
  exact outside query owned (by intro offset member; exact apart offset (List.mem_append_left _ member)) notCont

theorem MemoryCompletion.rank {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame cont base scratch oldLength oldCapacity length capacity pointer : BitVec 64} {ceiling : Nat}
    (completed : MemoryCompletion source post frame cont base scratch oldLength oldCapacity length capacity pointer ceiling)
    (ancestors : List (BitVec 64)) (limit : Nat)
    (owned : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      Arenas.Outside base scratch (ancestor + BitVec.ofNat 64 offset))
    (apart : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      (∀ field ∈ completionWriteOffsets, ancestor + BitVec.ofNat 64 offset ≠ frame + BitVec.ofNat 64 field) ∧
      ancestor + BitVec.ofNat 64 offset ≠ cont + 32#64)
    (cap : FrameSums.budget source.memory (frame :: ancestors) ≤ limit) :
    FrameRank.value limit post.memory (frame :: ancestors) false < FrameRank.value limit source.memory (frame :: ancestors) true ∧
      ImmediateDone post frame cont ∧
      FrameSums.budget post.memory (frame :: ancestors) = FrameSums.budget source.memory (frame :: ancestors) := by
  obtain ⟨paid, funded, clock, view, budget, used, cost, done, continuation, amortized, outside⟩ := completed
  have cells : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      post.memory (ancestor + BitVec.ofNat 64 offset) = source.memory (ancestor + BitVec.ofNat 64 offset) := by
    intro ancestor member offset inside
    exact outside _ (owned ancestor member offset inside) (apart ancestor member offset inside).1 (apart ancestor member offset inside).2
  have ancestorBudget := FrameSums.budget_congr source.memory post.memory ancestors cells
  have ancestorUsed := FrameSums.used_congr source.memory post.memory ancestors (by intro ancestor member; exact cells ancestor member 184 (by simp))
  have liveBudget : FrameSums.budget post.memory (frame :: ancestors) = FrameSums.budget source.memory (frame :: ancestors) := by
    change regularBudget post.memory frame + FrameSums.budget post.memory ancestors = regularBudget source.memory frame + FrameSums.budget source.memory ancestors
    rw [budget, ancestorBudget]
  have liveUsed : FrameSums.used source.memory (frame :: ancestors) ≤ FrameSums.used post.memory (frame :: ancestors) := by
    change (wordAt source.memory (frame + 184#64)).toNat + FrameSums.used source.memory ancestors ≤
      (wordAt post.memory (frame + 184#64)).toNat + FrameSums.used post.memory ancestors
    rw [ancestorUsed]
    exact Nat.add_le_add_right used _
  have bounded : FrameSums.used post.memory (frame :: ancestors) ≤ limit :=
    (FrameSums.used_le_budget post.memory _).trans (by rw [liveBudget]; exact cap)
  exact ⟨FrameRank.terminal limit source.memory post.memory _ _ (by simp) liveUsed bounded rfl, done, liveBudget⟩

theorem ImmediateDone.of_scopes {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {frame cont : BitVec 64}
    (done : ImmediateDone source frame cont) (same : emptyLocalsHOLFinite post = emptyLocalsHOLFinite source) :
    ImmediateDone post frame cont := by
  have memory := congrArg PanSemStateFiniteExact.memory same
  have mapped := congrArg PanSemStateFiniteExact.memaddrs same
  change post.memory = source.memory at memory
  change post.memaddrs = source.memaddrs at mapped
  cases done with
  | marked flag domain cell nonzero => exact .marked flag (by rw [mapped]; exact domain) (by rw [memory]; exact cell) nonzero
  | halted markDomain markCell haltDomain haltCell => exact .halted (by rw [mapped]; exact markDomain) (by rw [memory]; exact markCell) (by rw [mapped]; exact haltDomain) (by rw [memory]; exact haltCell)
  | exhausted active pc length markDomain markCell activeDomain activeCell nonzero pcDomain pcCell lengthDomain lengthCell finished =>
    exact .exhausted active pc length (by rw [mapped]; exact markDomain) (by rw [memory]; exact markCell)
      (by rw [mapped]; exact activeDomain) (by rw [memory]; exact activeCell) nonzero
      (by rw [mapped]; exact pcDomain) (by rw [memory]; exact pcCell)
      (by rw [mapped]; exact lengthDomain) (by rw [memory]; exact lengthCell) finished

theorem MemoryCompletion.of_scopes {source phase endpoint post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame cont base scratch oldLength oldCapacity length capacity pointer : BitVec 64} {ceiling : Nat}
    (completed : MemoryCompletion phase endpoint frame cont base scratch oldLength oldCapacity length capacity pointer ceiling)
    (start : emptyLocalsHOLFinite phase = emptyLocalsHOLFinite source)
    (finish : emptyLocalsHOLFinite post = emptyLocalsHOLFinite endpoint) :
    MemoryCompletion source post frame cont base scratch oldLength oldCapacity length capacity pointer ceiling := by
  obtain ⟨paid, funded, clock, view, budget, used, cost, done, continuation, amortized, outside⟩ := completed
  have sourceClock := congrArg PanSemStateFiniteExact.clock start
  have sourceMemory := congrArg PanSemStateFiniteExact.memory start
  have targetClock := congrArg PanSemStateFiniteExact.clock finish
  have targetMemory := congrArg PanSemStateFiniteExact.memory finish
  have globals := congrArg PanSemStateFiniteExact.globals finish
  change phase.clock = source.clock at sourceClock
  change phase.memory = source.memory at sourceMemory
  change post.clock = endpoint.clock at targetClock
  change post.memory = endpoint.memory at targetMemory
  change post.globals = endpoint.globals at globals
  have erased : Input.LocalEffects.erase post = Input.LocalEffects.erase endpoint := by
    have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with clock := 0}) finish
    exact same
  refine ⟨paid, ?_, ?_, view.after_erase erased, ?_, ?_, ?_, done.of_scopes finish, ?_, amortized, ?_⟩
  · rw [← sourceClock]; exact funded
  · rw [targetClock, clock, sourceClock]
  · rw [targetMemory, ← sourceMemory]; exact budget
  · rw [targetMemory, ← sourceMemory]; exact used
  · rw [targetMemory]; exact cost
  · rw [globals]; exact continuation
  · intro query owned apart notCont
    rw [targetMemory, ← sourceMemory]
    exact outside query owned apart notCont

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.MemoryTerminal.completion
#print axioms InitECandidate.Solver.GasBudget.RunFrames.MemoryCompletion.rank
#print axioms InitECandidate.Solver.GasBudget.RunFrames.ImmediateDone.of_scopes
#print axioms InitECandidate.Solver.GasBudget.RunFrames.MemoryCompletion.of_scopes
