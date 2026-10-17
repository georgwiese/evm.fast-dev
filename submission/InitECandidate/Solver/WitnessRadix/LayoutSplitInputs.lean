import InitECandidate.Solver.WitnessRadix.LayoutSplitMemory

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

/-- All per-store mapping, nonaliasing, hash-view and sorting ownership
premises are derived from the shared layout and current task interval. -/
theorem split_inputs {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (mapped : Mapped source layout) (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (sliceFor : BitVec 64 → Graph.Slice) (immutable : Immutable source layout context.keyFor sliceFor)
    (locals : SplitCount.TaskLocals source context)
    (rows : BuildCopy.Rows source.memory source.memaddrs context.src (BitVec.ofNat 64 context.start) 0 context.input)
    (inside : context.position < 256) (splitZero : 0 < zeroCount context)
    (splitOne : zeroCount context < context.input.length) (enough : 3 * context.input.length ≤ source.clock) :
    SplitCount.Inputs source context := by
  have countSmall := count_small layout valid
  have room := valid.room
  refine ⟨inside, (by have := atLayout.interval; omega), ?_, ?_, enough, splitZero, splitOne, locals,
    context_allocation_mapped source layout context allocated depth destination atLayout valid mapped branchRoom stackRoom,
    context_ready source layout context allocated depth destination atLayout valid mapped sliceFor immutable rows⟩
  · rw [atLayout.limitEq]
    exact atLayout.interval
  · rw [atLayout.dstEq, atLayout.limitEq]
    have bound : layout.backup.toNat + 8 * layout.capacity < 2 ^ 64 := valid.noWrap .backup
    omega

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.split_inputs
