import InitECandidate.Solver.Mpt.WitnessCoreRegistryConstructors
import InitECandidate.Solver.Mpt.WitnessNodeRegistryDecodePaths

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Register the actual completed extension with the full path bytes
borrowed from its real pending record. The actual old-memory frame and
pending/node separation protect that buffer through fresh allocation. -/
theorem NodeRegistry.extension_result_paths (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap finalHeap cursor limit nibbles length child : BitVec 64)
    (registry : NodeRegistry source frontier heap db) (paths : registry.PathModel) (above : cursor.toNat+7≤frontier) (frontierBefore : frontier≤heap.toNat)
    (frame : WitnessDecode.NormalFrame source post heap cursor limit) (view : ExtensionView post heap nibbles length child)
    (heapCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)))
    (before : heap.toNat+56≤finalHeap.toNat) (childMember : registry.graph.valid child)
    (path : TrieWalk.NibbleSpan source.memory source.memaddrs source.be nibbles length.toNat)
    (pathAligned : nibbles.toNat%8=0) (pathLower : frontier≤nibbles.toNat) (pathBefore : nibbles.toNat+length.toNat≤heap.toNat)
    (apart : ∀ index<length.toNat,∀ owner,registry.graph.valid owner → owner≠0#64 →
      ∀ offset<TrieWalk.nodeBytes (wordAt source.memory owner),
        panByteAlignHOL (width:=64) (byteAddress nibbles index)≠byteAddress owner offset) :
    ∃ next : NodeRegistry post frontier finalHeap db,next.PathModel ∧ next.graph.valid heap ∧
      (∀ pointer,registry.graph.valid pointer → next.graph.valid pointer) ∧
      (∀ pointer,next.graph.valid pointer → registry.graph.valid pointer ∨ pointer=heap) := by
  obtain ⟨old,oldValid⟩:=registry.after_normal_frame source post frontier heap heap db cursor limit (by omega) (Nat.le_refl _) frame
  have oldPaths:=paths.normal_frame source post frontier heap heap db cursor limit registry old oldValid above (Nat.le_refl _) frame
  have currentPath:=path.of_band source post nibbles length.toNat cursor.toNat heap.toNat pathAligned (by omega) pathBefore frame.domain frame.endian frame.memory
  have tags (owner : BitVec 64) (member : registry.graph.valid owner) (active : owner≠0#64) : wordAt post.memory owner=wordAt source.memory owner:=by
    have bounds:=registry.graph.footprint_bounds frontier heap.toNat registry.regions owner (.header owner member active)
    unfold wordAt
    rw [frame.memory owner (by omega) bounds.2]
  obtain ⟨actualHeap,actualCell,actualArena,actualAligned,grows⟩:=frame.nextHeap
  have same : actualHeap=finalHeap := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
  subst actualHeap
  let extended:=old.advance_heap post frontier heap finalHeap db grows
  have extendedPaths : extended.PathModel:=oldPaths.advance_heap post frontier heap finalHeap db old grows
  have member : extended.graph.valid child := by change old.graph.valid child; rw [oldValid]; exact childMember
  let data:=view.registration post heap nibbles length child extended.graph member
  have tag : wordAt post.memory heap=2#64 := by
    simp [wordAt,MemoryBytes.wordBits,show post.memory heap=.word 2#64 from by simpa only [BitVec.add_zero] using view.cells (0,2#64) (by simp)]
  have leaf : wordAt post.memory heap=1#64 → TrieWalk.ValueView post.memory post.memaddrs heap 48#64 56#64 1024 (WitnessValue db) := by
    intro impossible; rw [tag] at impossible; cases impossible
  let registered:=extended.register post frontier finalHeap db heap data leaf (fun _ _ notExtension=>(notExtension tag).elim)
    frontierBefore (by rw [tag]; change AllocatedBytes.Arena heap 56; exact view.arena) view.aligned
    (by rw [tag]; change heap.toNat+56≤finalHeap.toNat; exact before) (old.excludes_fresh post frontier heap db heap _ (Nat.le_refl _))
  have fields : wordAt post.memory (heap+32#64)=nibbles ∧ wordAt post.memory (heap+40#64)=length:=by
    constructor
    · simp [wordAt,view.cells (32,nibbles) (by simp),MemoryBytes.wordBits]
    · simp [wordAt,view.cells (40,length) (by simp),MemoryBytes.wordBits]
  have currentPaths : registered.PathModel:=by
    refine ⟨extendedPaths.bytes.register extended.graph post.be heap data ?_ ?_,
      extendedPaths.regions.register extended.graph frontier finalHeap.toNat heap data ?_,
      extendedPaths.separated.register extended.graph heap data ?_ ?_⟩
    · intro pathTag
      rw [fields.1,fields.2]
      exact currentPath
    · intro extensionTag
      rw [fields.2]
      exact view.pathPositive
    · intro pathTag
      rw [fields.1,fields.2]
      exact ⟨pathLower,by omega⟩
    · intro current member active pathTag index inside heapActive offset offsetInside
      have span:=oldPaths.bytes.span current member active pathTag
      have bounds:=oldPaths.regions current member active pathTag
      rw [tag] at offsetInside
      exact span.apart_before post.memory post.memaddrs post.be _ heap _ 56 view.arena bounds.2 index inside offset offsetInside
    · intro pathTag index inside owner ownerMember ownerActive offset offsetInside
      rw [fields.2] at inside
      rw [fields.1]
      rcases ownerMember with prior|fresh
      · have sourceMember : registry.graph.valid owner:=by change old.graph.valid owner at prior; rwa [oldValid] at prior
        rw [tags owner sourceMember ownerActive] at offsetInside
        exact apart index inside owner sourceMember ownerActive offset offsetInside
      · subst owner
        rw [tag] at offsetInside
        exact currentPath.apart_before post.memory post.memaddrs post.be nibbles heap length.toNat 56 view.arena pathBefore index inside offset offsetInside
  refine ⟨registered,currentPaths,Or.inr rfl,?_,?_⟩
  · intro pointer member
    change old.graph.valid pointer ∨ pointer=heap
    left; rw [oldValid]; exact member
  · intro pointer member
    change old.graph.valid pointer ∨ pointer=heap at member
    rcases member with prior|fresh
    · left; rw [←oldValid]; exact prior
    · exact Or.inr fresh

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.extension_result_paths
