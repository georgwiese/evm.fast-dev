import InitECandidate.Solver.WitnessRadix.LayoutContext
import InitECandidate.Solver.WitnessRadix.SplitLocals

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open SplitScope

def leftDestination (layout : Layout) (allocated : Nat) : Address :=
  (.keys, 32 * layout.count + 24 * allocated + 8)

theorem left_context (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) :
    ContextAt layout (SplitCount.leftContext context) (allocated + 1) (depth + 1) (leftDestination layout allocated) := by
  refine ⟨atLayout.srcEq, atLayout.dstEq, atLayout.keysEq, ?_, ?_, ?_, ?_,
    atLayout.pendingStartEq, atLayout.pendingCountEq, atLayout.pendingNodeEq, atLayout.limitEq, ?_, ?_⟩
  · change context.node + 24#64 = _
    rw [atLayout.nodeEq, branch_address_next]
  · change context.depth + 1#64 = _
    rw [atLayout.depthEq, BitVec.ofNat_add]
  · change context.node + 8#64 = cell layout .keys (32 * layout.count + 24 * allocated + 8)
    rw [atLayout.nodeEq]
    exact branch_address_field layout.keys layout.count allocated 1
  · exact ⟨allocated, by omega, 1, Or.inl rfl, rfl⟩
  · have length := List.length_filter_le (fun ordinal => !ScatterProgram.keep context.keyFor context.position ordinal) context.input
    have bound := atLayout.interval
    change context.start + (context.input.filter _).length ≤ layout.count
    omega
  · intro ordinal member
    exact atLayout.ordinals ordinal (List.mem_of_mem_filter member)

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.left_context
