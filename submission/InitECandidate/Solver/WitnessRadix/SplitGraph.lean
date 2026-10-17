import InitECandidate.Solver.WitnessRadix.SplitCountExecution
import InitECandidate.Solver.WitnessRadix.AllocationMemory
import InitECandidate.Solver.WitnessRadix.OpenGraphReplace

namespace InitECandidate.Solver.WitnessRadix.SplitCount
open Flapjack PanSemStateFiniteExact
open SplitScope

def writes (context : SplitContext) : List (BitVec 64 × BitVec 64) :=
  SplitProgram.allocationWrites context.node context.depth (BitVec.ofNat 64 context.start)
    (BitVec.ofNat 64 context.input.length) (BitVec.ofNat 64 (zeroCount context)) (BitVec.ofNat 64 context.position)
    context.dest context.pendingStart context.pendingCount context.pendingNode

theorem post_word {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (distinct : ((writes context).map Prod.fst).Nodup) (entry : BitVec 64 × BitVec 64)
    (member : entry ∈ writes context) : (post source context).memory entry.1 = .word entry.2 := by
  exact SplitProgram.branchMemory_words _ _ _ _ _ _ _ _ _ _ _ distinct entry member

/-- The literal allocation poststate installs a branch with two mapped holes.
No completed-subtree or successful-execution premise is assumed. -/
theorem new_branch {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (table keys vals : BitVec 64) (zero one : Graph.Tree)
    (distinct : ((writes context).map Prod.fst).Nodup)
    (mapped : SplitProgram.Mapped source context.node context.depth context.dest
      context.pendingStart context.pendingCount context.pendingNode)
    (nonzero : context.node ≠ 0#64) (even : context.node &&& 1#64 = 0#64) (inside : context.position < 256) :
    OpenGraph.Represents (post source context) table keys vals
      (.branch context.dest context.node context.position
        (.hole (context.node + 8#64) zero) (.hole (context.node + 16#64) one)) := by
  have nodeWord := post_word source context distinct (context.node, BitVec.ofNat 64 context.position)
    (by simp [writes, SplitProgram.allocationWrites])
  have destWord := post_word source context distinct (context.dest, context.node)
    (by simp [writes, SplitProgram.allocationWrites])
  exact ⟨mapped.destMapped, destWord, nonzero, even, inside, mapped.nodeMapped, nodeWord,
    rfl, rfl, mapped.zeroMapped, mapped.oneMapped⟩

theorem sortedMemory_away (memory : WordWrites.Memory) (context : SplitContext) (query : BitVec 64)
    (srcAway : ∀ offset < context.input.length,
      query ≠ BuildCopy.row context.src (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset))
    (dstAway : ∀ offset < context.input.length,
      query ≠ BuildCopy.row context.dst (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset)) :
    SortProgram.sortedMemory memory context.src context.dst context.keyFor context.position context.start context.input query =
      memory query := by
  unfold SortProgram.sortedMemory
  rw [BuildCopy.copyMemory_away, BuildCopy.copyMemory_away]
  · intro offset bound
    simpa only [Nat.zero_add] using dstAway offset (by simpa only [ScatterProgram.partition_length] using bound)
  · intro offset bound
    simpa only [Nat.zero_add] using srcAway offset (by simpa only [ScatterProgram.partition_length] using bound)

/-- Every write made by a complete split is either in its two ordinal
intervals or one of the seven explicit allocation/pending cells. -/
theorem post_away {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) (query : BitVec 64)
    (srcAway : ∀ offset < context.input.length,
      query ≠ BuildCopy.row context.src (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset))
    (dstAway : ∀ offset < context.input.length,
      query ≠ BuildCopy.row context.dst (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset))
    (allocationAway : query ∉ (writes context).map Prod.fst) :
    (post source context).memory query = source.memory query := by
  change SplitProgram.branchMemory _ _ _ _ _ _ _ _ _ _ _ query = _
  rw [SplitProgram.branchMemory_frame _ _ _ _ _ _ _ _ _ _ _ query allocationAway]
  exact sortedMemory_away source.memory context query srcAway dstAway

end InitECandidate.Solver.WitnessRadix.SplitCount

#print axioms InitECandidate.Solver.WitnessRadix.SplitCount.new_branch
#print axioms InitECandidate.Solver.WitnessRadix.SplitCount.post_away
