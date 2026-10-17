import InitECandidate.Solver.WitnessRadix.LayoutOwnership
import InitECandidate.Solver.WitnessRadix.LayoutWriteCells
import InitECandidate.Solver.WitnessRadix.SplitGraph

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

/-- Physical task addresses are derived from one fixed backing layout. -/
structure ContextAt (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address) : Prop where
  srcEq : context.src = layout.primary
  dstEq : context.dst = layout.backup
  keysEq : context.keys = layout.keys
  nodeEq : context.node = branchAddress layout.keys layout.count allocated
  depthEq : context.depth = BitVec.ofNat 64 depth
  destEq : context.dest = address layout destination
  incoming : IncomingOffset layout allocated destination.1 destination.2
  pendingStartEq : context.pendingStart = cell layout .primary (8 * layout.count)
  pendingCountEq : context.pendingCount = cell layout .backup (8 * layout.count)
  pendingNodeEq : context.pendingNode = cell layout .vals (8 * layout.count)
  limitEq : context.limit = layout.count
  interval : context.start + context.input.length ≤ layout.count
  ordinals : ∀ ordinal ∈ context.input, ordinal.toNat < layout.count

theorem allocation_cells (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) :
    (SplitCount.writes context).map Prod.fst =
      (allocationAddresses layout allocated depth destination).map (address layout) := by
  simp [SplitCount.writes, SplitProgram.allocationWrites, allocationAddresses,
    atLayout.nodeEq, atLayout.depthEq, atLayout.destEq,
    atLayout.pendingStartEq, atLayout.pendingCountEq, atLayout.pendingNodeEq,
    address, cell, base, branchAddress, byteAddress, BitVec.ofNat_add, BitVec.ofNat_mul, Nat.mul_comm, BitVec.add_assoc]

theorem context_ready {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination)
    (valid : Valid layout) (mapped : Mapped source layout)
    (sliceFor : BitVec 64 → Graph.Slice) (immutable : Immutable source layout context.keyFor sliceFor)
    (rows : BuildCopy.Rows source.memory source.memaddrs context.src (BitVec.ofNat 64 context.start) 0 context.input) :
    ScatterProgram.Ready source context.src context.dst (BitVec.ofNat 64 context.start) context.keys
      context.keyFor context.input 0 context.limit := by
  rw [atLayout.srcEq] at rows
  rw [atLayout.srcEq, atLayout.dstEq, atLayout.keysEq, atLayout.limitEq]
  exact ready source layout valid mapped context.keyFor sliceFor immutable context.input context.start
    atLayout.interval atLayout.ordinals rows

theorem allocation_distinct (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count) :
    ((SplitCount.writes context).map Prod.fst).Nodup := by
  rw [allocation_cells layout context allocated depth destination atLayout]
  apply addresses_nodup layout valid
  · intro entry member
    exact write_offset_bound layout valid _ _
      (allocation_address_write layout valid allocated depth destination branchRoom stackRoom atLayout.incoming entry member)
  · exact allocation_addresses_distinct layout allocated depth destination atLayout.incoming

theorem allocation_writable (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count) (word : BitVec 64)
    (member : word ∈ (SplitCount.writes context).map Prod.fst) :
    ∃ pool offset, WriteOffset layout pool offset ∧ word = cell layout pool offset := by
  rw [allocation_cells layout context allocated depth destination atLayout] at member
  obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
  exact ⟨entry.1, entry.2,
    allocation_address_write layout valid allocated depth destination branchRoom stackRoom atLayout.incoming entry entryMember, rfl⟩

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.allocation_cells
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.context_ready
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.allocation_distinct
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.allocation_writable
