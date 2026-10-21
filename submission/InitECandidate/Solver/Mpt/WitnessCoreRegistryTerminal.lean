import InitECandidate.Solver.Mpt.WitnessCoreRichInvariant
import InitECandidate.Solver.Mpt.TrieWalkValuesMap

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix
open Flapjack.Basis.Pure.MlString

def NodeRegistry.advance_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap nextHeap db : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (grows : heap.toNat≤nextHeap.toNat) : NodeRegistry source frontier nextHeap db :=
  ⟨registry.graph,registry.values,registry.regions.weaken registry.graph frontier heap.toNat frontier nextHeap.toNat (Nat.le_refl _) grows,registry.disjoint⟩

theorem NodeRegistry.excludes_fresh (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db node : BitVec 64) (size : Nat) (registry : NodeRegistry source frontier heap db)
    (fresh : heap.toNat≤node.toNat) : registry.graph.Excludes node size := by
  intro old member active
  exact Or.inl ((registry.regions old member active).2.2.2.trans fresh)

/-- A genuine decoder terminal result extends the completed registry by
its actual fresh leaf, or returns the already registered null pointer. -/
theorem NodeRegistry.decode_terminal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db pointer length heap finalHeap cursor limit node : BitVec 64)
    (registry : NodeRegistry source frontier heap db) (above : cursor.toNat≤frontier) (frontierBefore : frontier≤heap.toNat)
    (frame : WitnessDecode.NormalFrame source post heap cursor limit)
    (result : WitnessDecode.NormalResult post db pointer length heap cursor limit (.rStruct [.val (.word 0#64),.val (.word node)]))
    (heapCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap))) :
    ∃ next : NodeRegistry post frontier finalHeap db,next.graph.valid node ∧ (∀ child,registry.graph.valid child → next.graph.valid child) ∧
      (∀ child,next.graph.valid child → registry.graph.valid child ∨ child=node) := by
  obtain ⟨old,oldValid⟩:=registry.after_normal_frame source post frontier heap heap db cursor limit above (Nat.le_refl _) frame
  obtain ⟨actualHeap,actualCell,actualArena,actualAligned,grows⟩:=frame.nextHeap
  have same : actualHeap=finalHeap := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
  subst actualHeap
  let extended:=old.advance_heap post frontier heap finalHeap db grows
  cases result with
  | empty scratch=>
    exact ⟨extended,extended.graph.null,by intro child member; change old.graph.valid child; rw [oldValid]; exact member,by
      intro child member; left; change old.graph.valid child at member; rw [←oldValid]; exact member⟩
  | leaf node nibbles nibbleLength valuePointer valueLength actualHeap view freshPath freshNode scratch actualCell heapArena heapAligned nodeBefore=>
    have same : actualHeap=finalHeap := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
    subst actualHeap
    have tag : wordAt post.memory node=1#64 := by simp [wordAt,view.tag,MemoryBytes.wordBits]
    let data:=view.registration post node db pointer length nibbles nibbleLength valuePointer valueLength extended.graph
    let valueView:=TrieWalk.ValueView.map_extra post.memory post.memaddrs node 48#64 56#64 1024
      (fun p n=>2713731432≤p.toNat ∧ p.toNat+n.toNat≤db.toNat) (WitnessValue db) view.value (fun _ _ owned=>Or.inr owned)
    let registered:=extended.register post frontier finalHeap db node data (fun _=>valueView) (fun _ notLeaf _=>(notLeaf tag).elim)
      (frontierBefore.trans freshNode) (by rw [tag]; change AllocatedBytes.Arena node 64; exact view.arena) view.aligned
      (by rw [tag]; change node.toNat+64≤finalHeap.toNat; exact nodeBefore) (old.excludes_fresh post frontier heap db node _ freshNode)
    refine ⟨registered,?_,?_,?_⟩
    · change extended.graph.valid node ∨ node=node
      exact Or.inr rfl
    · intro child member
      change extended.graph.valid child ∨ child=node
      left
      change old.graph.valid child
      rw [oldValid]
      exact member
    · intro child member
      change extended.graph.valid child ∨ child=node at member
      rcases member with prior|same
      · left; change old.graph.valid child at prior; rw [←oldValid]; exact prior
      · exact Or.inr same

/-- A genuine resolver terminal extends the same registry by its actual
fresh hash node, or delivers null. Its HASH scratch write is in the real
normal frame and does not become a graph-closure assumption. -/
theorem NodeRegistry.resolve_terminal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap finalHeap cursor limit node : BitVec 64)
    (registry : NodeRegistry source frontier heap db) (above : cursor.toNat≤frontier) (frontierBefore : frontier≤heap.toNat)
    (frame : WitnessDecode.NormalFrame source post heap cursor limit)
    (result : Input.Main.RunAttemptConstructors.ResolveResult post db heap (resolveAnswer 0#64 node 0#64 0#64))
    (heapCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)))
    (domain : post.memaddrs=InitE.ordinaryDomain) (aligned : heap.toNat%8=0) :
    ∃ next : NodeRegistry post frontier finalHeap db,next.graph.valid node ∧ (∀ child,registry.graph.valid child → next.graph.valid child) ∧
      (∀ child,next.graph.valid child → registry.graph.valid child ∨ child=node) := by
  obtain ⟨old,oldValid⟩:=registry.after_normal_frame source post frontier heap heap db cursor limit above (Nat.le_refl _) frame
  obtain ⟨actualHeap,actualCell,actualArena,actualAligned,grows⟩:=frame.nextHeap
  have same : actualHeap=finalHeap := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
  subst actualHeap
  let extended:=old.advance_heap post frontier heap finalHeap db grows
  rcases result with empty|⟨valueEq,arena,stored,hashData,actualHeap,actualCell,finalArena,finalAligned,before⟩|
      ⟨pointer,length,pending,valueEq,small,lower,upper,hashSpan⟩
  · have zero : node=0#64 := by simpa [resolveAnswer] using empty
    rw [zero]
    exact ⟨extended,extended.graph.null,by intro child member; change old.graph.valid child; rw [oldValid]; exact member,by
      intro child member; left; change old.graph.valid child at member; rw [←oldValid]; exact member⟩
  · have same : node=heap := by simpa [resolveAnswer] using valueEq
    subst node
    have finalEq : actualHeap=finalHeap := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
    subst actualHeap
    have tag : wordAt post.memory heap=0#64 := by simp [wordAt,stored,MemoryBytes.wordBits]
    have mapped : post.memaddrs heap := by
      simpa only [byteAddress,BitVec.add_zero] using AllocatedBytes.word_mapped post heap 32 0 domain arena (by decide) aligned (by decide)
    let data:=TrieWalk.Registration.hashed post.memory post.memaddrs extended.graph heap mapped stored
    have leaf : wordAt post.memory heap=1#64 → TrieWalk.ValueView post.memory post.memaddrs heap 48#64 56#64 1024 (WitnessValue db) := by
      intro impossible; rw [tag] at impossible; cases impossible
    let registered:=extended.register post frontier finalHeap db heap data leaf (fun notHash _ _=>(notHash tag).elim)
      frontierBefore (by simpa only [tag,TrieWalk.nodeBytes,↓reduceIte] using arena) aligned
      (by simpa only [tag,TrieWalk.nodeBytes,↓reduceIte] using before) (old.excludes_fresh post frontier heap db heap _ (Nat.le_refl _))
    refine ⟨registered,?_,?_,?_⟩
    · change extended.graph.valid heap ∨ heap=heap
      exact Or.inr rfl
    · intro child member
      change extended.graph.valid child ∨ child=heap
      left
      change old.graph.valid child
      rw [oldValid]
      exact member
    · intro child member
      change extended.graph.valid child ∨ child=heap at member
      rcases member with prior|same
      · left; change old.graph.valid child at prior; rw [←oldValid]; exact prior
      · exact Or.inr same
  · simp [resolveAnswer] at valueEq

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.excludes_fresh
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.decode_terminal
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.resolve_terminal
