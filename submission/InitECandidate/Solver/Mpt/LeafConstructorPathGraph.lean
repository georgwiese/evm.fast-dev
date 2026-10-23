import InitECandidate.Solver.Mpt.NodeConstructorPhysical
import InitECandidate.Solver.Mpt.TriePathBufferPrefix
import InitECandidate.Solver.Mpt.TriePathRegisterFreshGraph
import InitECandidate.Solver.Mpt.ExtensionRegistration

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- The actual original leaf construction preserves all older nodes
and paths and registers the fresh node with its borrowed full path. -/
theorem Physical.leaf_path_graph
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (words : String → BitVec 64)
    (physical : Physical .leaf source target heap words) (domain : source.memaddrs=InitE.ordinaryDomain) (aligned : heap.toNat%8=0)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (floor : nodeLower≤heap.toNat) (buffer : graph.PathBuffer source.be pathLower heap.toNat (words "nib") (words "nlen").toNat)
    (payload : TrieWalk.Payload source.memaddrs (words "vptr") (words "vlen") limit) (extra : property (words "vptr") (words "vlen")) :
    ∃ next : TrieWalk.Graph target.memory target.memaddrs,
      (∀ node,next.valid node ↔ graph.valid node ∨ node=heap) ∧ next.valid heap ∧
      next.Regions nodeLower (PersistentAlloc.rounded heap 64#64).toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
      next.PathBytes target.be ∧ next.PathRegions pathLower (PersistentAlloc.rounded heap 64#64).toNat ∧ next.PathSeparated := by
  have memory : ∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query:=
    fun query before=>physical.memory query (Or.inl before)
  obtain ⟨base,same,baseRegions,baseDisjoint,⟨baseValues⟩,basePaths,basePathRegions,baseSeparated⟩:=
    graph.after_path_prefix source target limit nodeLower pathLower heap.toNat property values regions disjoint paths pathRegions separated physical.domain physical.endian memory
  have currentBuffer:=buffer.of_prefix source target graph base pathLower heap.toNat nodeLower (words "nib") (words "nlen").toNat regions same physical.domain physical.endian memory
  have targetDomain : target.memaddrs=InitE.ordinaryDomain:=physical.domain.trans domain
  have tagCell : target.memory heap=.word 1#64:=by
    simpa [FieldStores.Value.word] using physical.cells ⟨0,.literal 1#64⟩ (by simp [fields])
  have pointerCell : target.memory (heap+32#64)=.word (words "nib"):=by
    simpa [FieldStores.Value.word] using physical.cells ⟨32,.saved "nib" (words "nib")⟩ (by simp [fields])
  have lengthCell : target.memory (heap+40#64)=.word (words "nlen"):=by
    simpa [FieldStores.Value.word] using physical.cells ⟨40,.saved "nlen" (words "nlen")⟩ (by simp [fields])
  have fits : (words "nib").toNat+min (words "nlen").toNat 64<2^64:=by have full:=buffer.span.fits; omega
  have mapped : ∀ offset<min (words "nlen").toNat 64,target.memaddrs (panByteAlignHOL (width:=64) (byteAddress (words "nib") offset)):=by
    intro offset inside
    exact currentBuffer.span.mapped offset (by omega)
  have valuePointerCell : target.memory (heap+48#64)=.word (words "vptr"):=by
    simpa [FieldStores.Value.word] using physical.cells ⟨48,.saved "vptr" (words "vptr")⟩ (by simp [fields])
  have valueLengthCell : target.memory (heap+56#64)=.word (words "vlen"):=by
    simpa [FieldStores.Value.word] using physical.cells ⟨56,.saved "vlen" (words "vlen")⟩ (by simp [fields])
  let data:=TrieWalk.Registration.leaf target base heap (words "nib") (words "nlen") targetDomain physical.arena aligned tagCell pointerCell lengthCell fits mapped
  have newValue : TrieWalk.ValueView target.memory target.memaddrs heap 48#64 56#64 limit property:=
    TrieWalk.ValueView.leaf target heap (words "vptr") (words "vlen") limit property targetDomain physical.arena aligned valuePointerCell valueLengthCell
      (by rw [physical.domain]; exact payload) extra
  have actualTag : wordAt target.memory heap=1#64:=by simp [wordAt,tagCell,MemoryBytes.wordBits]
  have pointerStored : wordAt target.memory (heap+32#64)=words "nib":=by simp [wordAt,pointerCell,MemoryBytes.wordBits]
  have lengthStored : wordAt target.memory (heap+40#64)=words "nlen":=by simp [wordAt,lengthCell,MemoryBytes.wordBits]
  have nodeArena : AllocatedBytes.Arena heap (TrieWalk.nodeBytes (wordAt target.memory heap)):=by
    simpa [actualTag,TrieWalk.nodeBytes,bytes] using physical.arena
  have before : heap.toNat+TrieWalk.nodeBytes (wordAt target.memory heap)≤(PersistentAlloc.rounded heap 64#64).toNat:=by
    simpa [actualTag,TrieWalk.nodeBytes,bytes] using physical.before
  obtain ⟨nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    base.register_fresh_path target.be limit nodeLower pathLower heap.toNat (PersistentAlloc.rounded heap 64#64).toNat property
      baseValues baseRegions baseDisjoint basePaths basePathRegions baseSeparated heap (words "nib") (words "nlen") data
      (Or.inl actualTag) pointerStored lengthStored
      (by intro extensionTag; rw [actualTag] at extensionTag; cases extensionTag) nodeArena aligned floor (Nat.le_refl _) before currentBuffer (fun _=>newValue)
  refine ⟨base.register heap data,?_,Or.inr rfl,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩
  intro node
  change (base.valid node ∨ node=heap) ↔ (graph.valid node ∨ node=heap)
  rw [same]

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.Physical.leaf_path_graph
