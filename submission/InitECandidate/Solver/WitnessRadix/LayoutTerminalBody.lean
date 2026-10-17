import InitECandidate.Solver.WitnessRadix.LayoutTerminalCells
import InitECandidate.Solver.WitnessRadix.LayoutLeafMemory
import InitECandidate.Solver.WitnessRadix.TerminalLoopContinue

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

theorem tag_word (ordinal : BitVec 64) : WordBits.leafTag ordinal.toNat = ordinal * 2#64 + 1#64 := by
  simp [WordBits.leafTag, BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.mul_comm]

theorem terminal_test_read {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (locals : SplitCount.TaskLocals source context)
    (stop : context.input.length = 1 ∨ context.position = 256) :
    QueryBranch.eval source TerminalProgram.terminalTest = some (.val (.word 1#64)) := by
  have selected : BitVec.ofNat 64 context.input.length = 1#64 ∨ BitVec.ofNat 64 context.position = 256#64 := by
    rcases stop with single | lastBit
    · exact Or.inl (by rw [single])
    · exact Or.inr (by rw [lastBit])
  simpa only [if_pos selected] using TerminalProgram.terminal_test source _ _ locals.countLocal locals.bitLocal

/-- Complete actual terminal body with a pending sibling, deriving every pop
read, store-safety condition and ordinal load from the common invariant. -/
theorem terminal_body_continue {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout) (mapped : Mapped source layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (locals : SplitCount.TaskLocals source context)
    (rows : BuildCopy.Rows source.memory source.memaddrs context.src (BitVec.ofNat 64 context.start) 0 context.input)
    (stop : context.input.length = 1 ∨ context.position = 256) (ordinal : BitVec 64) (last : context.input.getLast? = some ordinal)
    (task : PendingStack.Task) (rest : List PendingStack.Task) (length : (task :: rest).length = depth)
    (parents : ParentsWithin layout allocated (task :: rest))
    (rep : PendingStack.Represents source context.pendingStart context.pendingCount context.pendingNode (task :: rest)) :
    evaluateHOLFiniteState source BuildEntry.mainBody =
      (some .continue, PopProgram.popPost (OpenGraph.leafPost source context.dest ordinal.toNat) context.depth
        (BitVec.ofNat 64 task.start) (BitVec.ofNat 64 task.input.length) task.parent (BitVec.ofNat 64 task.parentPosition)) := by
  have countSmall := count_small layout valid
  have depthPositive : 0 < depth := by rw [← length]; simp
  have depthSmall : depth < 2 ^ 64 := by omega
  have nonzero : context.depth ≠ 0#64 := by
    intro zero
    have numeric := congrArg BitVec.toNat zero
    rw [atLayout.depthEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt depthSmall] at numeric
    change depth = 0 at numeric
    omega
  obtain ⟨pool, offset, write, destEq⟩ := destination_writable layout context allocated depth destination atLayout branchRoom
  have destinationMapped : source.memaddrs context.dest := by
    rw [destEq]
    have bound := write_word_bound layout valid pool offset write
    exact mapped pool offset bound.2 bound.1
  have run := TerminalProgram.main_body_continue source context.depth (BitVec.ofNat 64 context.start)
    (BitVec.ofNat 64 context.input.length) (BitVec.ofNat 64 context.position) context.dest
    context.pendingStart context.pendingCount context.pendingNode (BitVec.ofNat 64 task.start)
    (BitVec.ofNat 64 task.input.length) task.parent (BitVec.ofNat 64 task.parentPosition) ordinal nonzero
    (terminal_test_read source context locals stop)
    (BuildCopy.terminal_read source context.src context.start context.input ordinal locals.srcLocal locals.startLocal locals.countLocal rows last)
    (terminal_locals source context locals)
    (terminal_head_cells source layout context allocated depth destination atLayout task rest length rep)
    (terminal_store_safe layout context allocated depth destination atLayout valid branchRoom stackRoom task rest length parents) destinationMapped
  simpa only [OpenGraph.leafPost, tag_word] using run

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.terminal_body_continue
