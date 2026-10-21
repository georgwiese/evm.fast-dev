import InitECandidate.Solver.Mpt.WitnessCoreRegistryTerminal

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual completed extension fields and real old-storage frame
register its fresh56-byte node and already completed child. -/
theorem NodeRegistry.extension_result (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap finalHeap cursor limit nibbles length child : BitVec 64)
    (registry : NodeRegistry source frontier heap db) (above : cursor.toNat≤frontier) (frontierBefore : frontier≤heap.toNat)
    (frame : WitnessDecode.NormalFrame source post heap cursor limit) (view : ExtensionView post heap nibbles length child)
    (heapCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)))
    (before : heap.toNat+56≤finalHeap.toNat) (childMember : registry.graph.valid child) :
    ∃ next : NodeRegistry post frontier finalHeap db,next.graph.valid heap ∧
      (∀ pointer,registry.graph.valid pointer → next.graph.valid pointer) ∧
      (∀ pointer,next.graph.valid pointer → registry.graph.valid pointer ∨ pointer=heap) := by
  obtain ⟨old,oldValid⟩:=registry.after_normal_frame source post frontier heap heap db cursor limit above (Nat.le_refl _) frame
  obtain ⟨actualHeap,actualCell,actualArena,actualAligned,grows⟩:=frame.nextHeap
  have same : actualHeap=finalHeap := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
  subst actualHeap
  let extended:=old.advance_heap post frontier heap finalHeap db grows
  have member : extended.graph.valid child := by change old.graph.valid child; rw [oldValid]; exact childMember
  let data:=view.registration post heap nibbles length child extended.graph member
  have tag : wordAt post.memory heap=2#64 := by
    simp [wordAt,MemoryBytes.wordBits,show post.memory heap=.word 2#64 from by simpa only [BitVec.add_zero] using view.cells (0,2#64) (by simp)]
  have leaf : wordAt post.memory heap=1#64 → TrieWalk.ValueView post.memory post.memaddrs heap 48#64 56#64 1024 (WitnessValue db) := by
    intro impossible; rw [tag] at impossible; cases impossible
  let registered:=extended.register post frontier finalHeap db heap data leaf (fun _ _ notExtension=>(notExtension tag).elim)
    frontierBefore (by rw [tag]; change AllocatedBytes.Arena heap 56; exact view.arena) view.aligned
    (by rw [tag]; change heap.toNat+56≤finalHeap.toNat; exact before) (old.excludes_fresh post frontier heap db heap _ (Nat.le_refl _))
  refine ⟨registered,Or.inr rfl,?_,?_⟩
  · intro pointer member
    change old.graph.valid pointer ∨ pointer=heap
    left; rw [oldValid]; exact member
  · intro pointer member
    change old.graph.valid pointer ∨ pointer=heap at member
    rcases member with prior|fresh
    · left; rw [←oldValid]; exact prior
    · exact Or.inr fresh

/-- A completed branch is registered only after its sixteen actual
child words, real final value and excluded176-byte allocation are known. -/
theorem NodeRegistry.branch_result (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap node : BitVec 64) (registry : NodeRegistry post frontier heap db)
    (children : Children post registry.graph.valid node 16)
    (value : TrieWalk.ValueView post.memory post.memaddrs node 160#64 168#64 1024 (WitnessValue db))
    (domain : post.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena node 176) (aligned : node.toNat%8=0)
    (stored : post.memory node=.word 3#64) (floor : frontier≤node.toNat) (before : node.toNat+176≤heap.toNat)
    (excluded : registry.graph.Excludes node 176) :
    ∃ next : NodeRegistry post frontier heap db,next.graph.valid node ∧
      (∀ pointer,registry.graph.valid pointer → next.graph.valid pointer) ∧
      (∀ pointer,next.graph.valid pointer → registry.graph.valid pointer ∨ pointer=node) := by
  let data:=children.registration post registry.graph node domain arena aligned stored
  have tag : wordAt post.memory node=3#64 := by simp [wordAt,stored,MemoryBytes.wordBits]
  have leaf : wordAt post.memory node=1#64 → TrieWalk.ValueView post.memory post.memaddrs node 48#64 56#64 1024 (WitnessValue db) := by
    intro impossible; rw [tag] at impossible; cases impossible
  let registered:=registry.register post frontier heap db node data leaf (fun _ _ _=>value) floor
    (by rw [tag]; change AllocatedBytes.Arena node 176; exact arena) aligned (by rw [tag]; change node.toNat+176≤heap.toNat; exact before)
    (by simpa only [tag,show TrieWalk.nodeBytes 3#64=176 from by decide] using excluded)
  exact ⟨registered,Or.inr rfl,fun _ member=>Or.inl member,fun _ member=>member⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.extension_result
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.branch_result
