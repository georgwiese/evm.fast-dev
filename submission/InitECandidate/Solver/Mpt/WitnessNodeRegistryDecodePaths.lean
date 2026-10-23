import InitECandidate.Solver.Mpt.WitnessNodeRegistryPathModel
import InitECandidate.Solver.Mpt.WitnessCoreRegistryTerminal
import InitECandidate.Solver.Mpt.WitnessDecodeResultNibbles
import InitECandidate.Solver.Mpt.TriePathBytesSeparation

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem NodeRegistry.PathModel.advance_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap next db : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (paths : registry.PathModel) (grows : heap.toNat≤next.toNat) :
    (registry.advance_heap source frontier heap next db grows).PathModel :=
  ⟨paths.bytes,paths.regions.weaken registry.graph frontier heap.toNat frontier next.toNat (Nat.le_refl _) grows,paths.separated⟩

/-- The actual strong decoder result registers its fresh leaf's full
path bytes. Real allocation order proves separation in both directions:
old paths/new node and new path/old nodes, as well as the leaf's own path. -/
theorem NodeRegistry.decode_terminal_paths (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db pointer length heap finalHeap cursor limit node : BitVec 64)
    (registry : NodeRegistry source frontier heap db) (paths : registry.PathModel)
    (above : cursor.toNat+7≤frontier) (frontierBefore : frontier≤heap.toNat)
    (frame : WitnessDecode.NormalFrame source post heap cursor limit)
    (result : WitnessDecode.NibbleResult post db pointer length heap cursor limit (.rStruct [.val (.word 0#64),.val (.word node)]))
    (heapCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap))) :
    ∃ next : NodeRegistry post frontier finalHeap db,next.PathModel ∧ next.graph.valid node ∧
      (∀ child,registry.graph.valid child → next.graph.valid child) ∧
      (∀ child,next.graph.valid child → registry.graph.valid child ∨ child=node) := by
  obtain ⟨old,oldValid⟩:=registry.after_normal_frame source post frontier heap heap db cursor limit (by omega) (Nat.le_refl _) frame
  have oldPaths:=paths.normal_frame source post frontier heap heap db cursor limit registry old oldValid above (Nat.le_refl _) frame
  obtain ⟨actualHeap,actualCell,actualArena,actualAligned,grows⟩:=frame.nextHeap
  have same : actualHeap=finalHeap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
  subst actualHeap
  let extended:=old.advance_heap post frontier heap finalHeap db grows
  have extendedPaths : extended.PathModel:=oldPaths.advance_heap post frontier heap finalHeap db old grows
  cases result with
  | empty scratch=>
    exact ⟨extended,extendedPaths,extended.graph.null,
      by intro child member; change old.graph.valid child; rw [oldValid]; exact member,
      by intro child member; left; change old.graph.valid child at member; rw [←oldValid]; exact member⟩
  | leaf node nibbles nibbleLength valuePointer valueLength actualHeap view freshPath freshNode scratch actualCell heapArena heapAligned nodeBefore pathBytes pathAligned pathBefore=>
    have same : actualHeap=finalHeap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
    subst actualHeap
    have tag : wordAt post.memory node=1#64:=by simp [wordAt,view.tag,MemoryBytes.wordBits]
    have fields : wordAt post.memory (node+32#64)=nibbles ∧ wordAt post.memory (node+40#64)=nibbleLength:=by
      constructor
      · simp [wordAt,view.cells (32,nibbles) (by simp),MemoryBytes.wordBits]
      · simp [wordAt,view.cells (40,nibbleLength) (by simp),MemoryBytes.wordBits]
    let data:=view.registration post node db pointer length nibbles nibbleLength valuePointer valueLength extended.graph
    let valueView:=TrieWalk.ValueView.map_extra post.memory post.memaddrs node 48#64 56#64 1024
      (fun p n=>2713731432≤p.toNat ∧ p.toNat+n.toNat≤db.toNat) (WitnessValue db) view.value (fun _ _ owned=>Or.inr owned)
    let registered:=extended.register post frontier finalHeap db node data (fun _=>valueView) (fun _ notLeaf _=>(notLeaf tag).elim)
      (frontierBefore.trans freshNode) (by rw [tag]; change AllocatedBytes.Arena node 64; exact view.arena) view.aligned
      (by rw [tag]; change node.toNat+64≤finalHeap.toNat; exact nodeBefore) (old.excludes_fresh post frontier heap db node _ freshNode)
    have currentPaths : registered.PathModel:=by
      refine ⟨extendedPaths.bytes.register extended.graph post.be node data ?_ ?_,
        extendedPaths.regions.register extended.graph frontier finalHeap.toNat node data ?_,
        extendedPaths.separated.register extended.graph node data ?_ ?_⟩
      · intro pathTag
        rw [fields.1,fields.2]
        exact pathBytes
      · intro impossible
        rw [tag] at impossible
        cases impossible
      · intro pathTag
        rw [fields.1,fields.2]
        exact ⟨frontierBefore.trans freshPath,by omega⟩
      · intro current member active pathTag index inside nodeActive offset offsetInside
        have span:=oldPaths.bytes.span current member active pathTag
        have bounds:=oldPaths.regions current member active pathTag
        rw [tag] at offsetInside
        exact span.apart_before post.memory post.memaddrs post.be _ node _ 64 view.arena (bounds.2.trans freshNode) index inside offset offsetInside
      · intro pathTag index inside owner ownerMember ownerActive offset offsetInside
        rw [fields.2] at inside
        rw [fields.1]
        rcases ownerMember with prior|fresh
        · obtain ⟨floor,arena,aligned,before⟩:=old.regions owner prior ownerActive
          exact pathBytes.apart_after post.memory post.memaddrs post.be nibbles owner nibbleLength.toNat _ pathAligned arena
            (before.trans freshPath) index inside offset offsetInside
        · subst owner
          rw [tag] at offsetInside
          exact pathBytes.apart_before post.memory post.memaddrs post.be nibbles node nibbleLength.toNat 64 view.arena pathBefore index inside offset offsetInside
    refine ⟨registered,currentPaths,?_,?_,?_⟩
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

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.PathModel.advance_heap
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.decode_terminal_paths
