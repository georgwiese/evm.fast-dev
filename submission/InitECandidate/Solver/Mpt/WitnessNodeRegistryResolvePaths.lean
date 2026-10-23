import InitECandidate.Solver.Mpt.WitnessNodeRegistryDecodePaths

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual resolver database band protects every completed path. -/
theorem NodeRegistry.PathModel.database_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db : BitVec 64)
    (registry : NodeRegistry source frontier heap db) (next : NodeRegistry target frontier heap db)
    (paths : registry.PathModel) (validEq : next.graph.valid=registry.graph.valid)
    (scratchBelow : 2713717616+7≤frontier)
    (frame : DatabaseFrame source target heap) : next.PathModel := by
  have agree : ∀ query,registry.graph.Footprint query→target.memory query=source.memory query:=by
    intro query required
    have bounds:=registry.graph.footprint_bounds frontier heap.toNat registry.regions query required
    exact frame.memory query (by omega) bounds.2
  have bytes : ∀ node,registry.graph.valid node→node≠0#64→(wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64)→
      ∀ index<(wordAt source.memory (node+40#64)).toNat,
        target.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index))=
        source.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)):=by
    intro node member active tag index inside
    have span:=paths.bytes.span node member active tag
    have bounds:=paths.regions node member active tag
    have number:=byteAddress_toNat (wordAt source.memory (node+32#64)) index (by have fits:=span.fits; omega)
    apply frame.memory
    · rw [AllocatedBytes.aligned_number,number]
      omega
    · rw [AllocatedBytes.aligned_number,number]
      omega
  exact ⟨paths.bytes.of_agreement source.memory target.memory source.memaddrs target.memaddrs source.be target.be
      registry.graph next.graph validEq frame.domain frame.endian agree bytes,
    paths.regions.of_agreement source.memory target.memory source.memaddrs target.memaddrs registry.graph next.graph frontier heap.toNat validEq agree,
    paths.separated.of_agreement source.memory target.memory source.memaddrs target.memaddrs registry.graph next.graph validEq agree⟩

theorem NodeRegistry.resolve_terminal_paths (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap finalHeap node : BitVec 64)
    (registry : NodeRegistry source frontier heap db) (paths : registry.PathModel) (above : 2713717616+7≤frontier) (frontierBefore : frontier≤heap.toNat)
    (frame : DatabaseFrame source post heap) (grows : heap.toNat≤finalHeap.toNat)
    (result : Input.Main.RunAttemptConstructors.ResolveResult post db heap (resolveAnswer 0#64 node 0#64 0#64))
    (heapCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)))
    (domain : post.memaddrs=InitE.ordinaryDomain) (aligned : heap.toNat%8=0) :
    ∃ next : NodeRegistry post frontier finalHeap db,next.PathModel ∧ next.graph.valid node ∧ (∀ child,registry.graph.valid child → next.graph.valid child) ∧
      (∀ child,next.graph.valid child → registry.graph.valid child ∨ child=node) := by
  obtain ⟨old,oldValid⟩:=registry.after_database_frame source post frontier heap db (by omega) frame
  have oldPaths:=paths.database_frame source post frontier heap db registry old oldValid above frame
  let extended:=old.advance_heap post frontier heap finalHeap db grows
  have extendedPaths : extended.PathModel:=oldPaths.advance_heap post frontier heap finalHeap db old grows
  rcases result with empty|⟨valueEq,arena,stored,hashData,actualHeap,actualCell,finalArena,finalAligned,before⟩|
      ⟨pointer,length,pending,valueEq,small,lower,upper,hashSpan⟩
  · have zero : node=0#64 := by simpa [resolveAnswer] using empty
    rw [zero]
    exact ⟨extended,extendedPaths,extended.graph.null,by intro child member; change old.graph.valid child; rw [oldValid]; exact member,by
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
    have currentPaths : registered.PathModel:=by
      refine ⟨extendedPaths.bytes.register extended.graph post.be heap data ?_ ?_,
        extendedPaths.regions.register extended.graph frontier finalHeap.toNat heap data ?_,
        extendedPaths.separated.register extended.graph heap data ?_ ?_⟩
      · intro pathTag
        rw [tag] at pathTag
        rcases pathTag with impossible|impossible <;> cases impossible
      · intro impossible
        rw [tag] at impossible
        cases impossible
      · intro pathTag
        rw [tag] at pathTag
        rcases pathTag with impossible|impossible <;> cases impossible
      · intro current member active pathTag index inside heapActive offset offsetInside
        have span:=oldPaths.bytes.span current member active pathTag
        have bounds:=oldPaths.regions current member active pathTag
        rw [tag] at offsetInside
        exact span.apart_before post.memory post.memaddrs post.be _ heap _ 32 arena bounds.2 index inside offset offsetInside
      · intro pathTag
        rw [tag] at pathTag
        rcases pathTag with impossible|impossible <;> cases impossible
    refine ⟨registered,currentPaths,?_,?_,?_⟩
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

#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.PathModel.database_frame
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.resolve_terminal_paths
