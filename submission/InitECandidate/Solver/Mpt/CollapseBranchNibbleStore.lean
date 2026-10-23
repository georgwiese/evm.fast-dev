import InitECandidate.Solver.Mpt.CollapseBranchSuffixProgram
import InitECandidate.Solver.Mpt.TriePathBytesStore
import InitECandidate.Solver.Mpt.TriePathBufferPrefix
import InitECandidate.Solver.Mpt.TriePathBufferBounds
import InitECandidate.Solver.WitnessRadix.ByteStoreWord

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def nibblePost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (nibble index : BitVec 64):=
  {source with memory:=ByteStore.put source.memory source.be nibble (BitVec.ofNat 8 index.toNat)}

/-- The actual original selected-nibble store initializes a real protected
one-byte path and retains the entire old graph and every older memory word.
The caller derives the eight-byte arena from its actual allocation. -/
theorem nibble_store_paths (source : PanSemStateFiniteExact 64 Guest.HostMemory) (nibble index nextHeap : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower nibble.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower nibble.toNat) (separated : graph.PathSeparated)
    (lower : pathLower≤nibble.toNat) (room : nibble.toNat+8≤nextHeap.toNat)
    (arena : AllocatedBytes.Arena nibble 8) (aligned : nibble.toNat%8=0) (bounded : index.toNat<16)
    (nibbleCell : source.locals.lookup (ofString "nib")=some (.val (.word nibble)))
    (indexCell : source.locals.lookup (ofString "idx")=some (.val (.word index)))
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) :
    evaluateHOLFiniteState source nibbleStore=(none,nibblePost source nibble index) ∧
      (∀ query : BitVec 64,query.toNat<nibble.toNat → (nibblePost source nibble index).memory query=source.memory query) ∧
      ∃ next : TrieWalk.Graph (nibblePost source nibble index).memory (nibblePost source nibble index).memaddrs,
        next.valid=graph.valid ∧ next.Regions nodeLower nextHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
        next.PathBytes (nibblePost source nibble index).be ∧ next.PathRegions pathLower nextHeap.toNat ∧ next.PathSeparated ∧
        next.PathBuffer (nibblePost source nibble index).be pathLower nextHeap.toNat nibble 1 := by
  let post:=nibblePost source nibble index
  have mapped : source.memaddrs (panByteAlignHOL (width:=64) nibble):=by
    simpa only [byteAddress,BitVec.add_zero] using AllocatedBytes.byte_mapped source nibble 8 0 domain arena (by decide)
  have nibbleRead : eval source (localVar "nib")=some (.val (.word nibble)):=by simp [eval,localVar,evalHOLExact,toExact,nibbleCell]
  have indexRead : eval source (localVar "idx")=some (.val (.word index)):=by simp [eval,localVar,evalHOLExact,toExact,indexCell]
  have actual : evaluateHOLFiniteState source nibbleStore=(none,post):=by
    rw [child_shapes.2.2.2.2.2.2]
    exact ByteStore.execute_word source (localVar "nib") (localVar "idx") nibble index nibbleRead indexRead mapped
  have older (query : BitVec 64) (before : query.toNat<nibble.toNat) : post.memory query=source.memory query:=
    TrieWalk.byte_store_before source.memory source.be nibble query (BitVec.ofNat 8 index.toNat) aligned before
  have span : TrieWalk.NibbleSpan post.memory post.memaddrs post.be nibble 1:=by
    have full:=TrieWalk.NibbleSpan.stored_byte source.memory source.memaddrs nibble index (by have upper:=arena.upper; omega) bounded mapped
    simpa only [post,nibblePost,little] using full
  obtain ⟨next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    graph.after_path_prefix source post limit nodeLower pathLower nibble.toNat property values regions disjoint paths pathRegions separated rfl rfl older
  have fresh:=TrieWalk.Graph.PathBuffer.fresh next post.be nodeLower nibble.toNat nextHeap.toNat nibble 1 nextRegions aligned span (Nat.le_refl _) (by omega)
  refine ⟨actual,older,next,same,?_,nextDisjoint,nextValues,nextPaths,?_,nextSeparated,?_⟩
  · intro node member active
    obtain ⟨floor,physical,alignment,before⟩:=nextRegions node member active
    exact ⟨floor,physical,alignment,before.trans (by omega)⟩
  · exact TrieWalk.Graph.PathRegions.weaken next pathLower nibble.toNat pathLower nextHeap.toNat nextPathRegions (Nat.le_refl _) (by omega)
  · exact fresh.weaken next post.be nibble.toNat nextHeap.toNat pathLower nextHeap.toNat nibble 1 lower (Nat.le_refl _)

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.nibble_store_paths
