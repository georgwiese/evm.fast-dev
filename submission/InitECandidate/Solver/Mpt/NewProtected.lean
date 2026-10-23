import InitECandidate.Solver.Mpt.NewCall
import InitECandidate.Solver.Mpt.SetHeader

namespace InitECandidate.Solver.Mpt.NewTrie
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget

/-- The two stores performed by the original map allocator preserve the
entire already decoded graph. The actual new header follows those nodes
and paths and is protected from subsequent trie updates. -/
theorem post_graph (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap root flag : BitVec 64) (arena : AllocatedBytes.Arena heap 16) (aligned : heap.toNat%8=0)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat)
    (property : BitVec 64→BitVec 64→Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (member : graph.valid root) :
    graph.PathFields (post source heap root flag).memory ∧
      ∃ next : TrieWalk.Graph (post source heap root flag).memory (post source heap root flag).memaddrs,
        next.valid=graph.valid ∧ next.Regions nodeLower (PersistentAlloc.rounded heap 16#64).toNat ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes source.be ∧
        next.PathRegions pathLower (PersistentAlloc.rounded heap 16#64).toNat ∧ next.PathSeparated ∧
        SetTrie.Header (post source heap root flag) next heap root flag := by
  have flagNumber : (heap+8#64).toNat=heap.toNat+8:=byteAddress_toNat heap 8 (by have upper:=arena.upper; omega)
  have rootSafe:=TrieWalk.Graph.ProtectedWord.above_regions graph source.be nodeLower pathLower heap.toNat heap regions paths pathRegions (Nat.le_refl _)
  have flagSafe:=TrieWalk.Graph.ProtectedWord.above_regions graph source.be nodeLower pathLower heap.toNat (heap+8#64) regions paths pathRegions (by rw [flagNumber]; omega)
  let middle:={source with memory:=StoreWord.put source.memory heap root}
  obtain ⟨firstFields,first,firstSame,firstRegions,firstDisjoint,⟨firstValues⟩,firstPaths,firstPathRegions,firstSeparated⟩:=
    graph.after_protected_store source heap root limit nodeLower pathLower heap.toNat property values regions disjoint paths pathRegions separated rootSafe
  have firstFlag:=flagSafe.of_fields graph first (heap+8#64) firstSame firstFields
  obtain ⟨lastFields,next,lastSame,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    first.after_protected_store middle (heap+8#64) flag limit nodeLower pathLower heap.toNat property
      firstValues firstRegions firstDisjoint firstPaths firstPathRegions firstSeparated firstFlag
  have fields:=firstFields.trans graph first lastFields (by intro node live; rw [firstSame]; exact live)
  have same:=lastSame.trans firstSame
  have grows : heap.toNat≤(PersistentAlloc.rounded heap 16#64).toNat:=by
    have growth:=(PersistentAlloc.guards heap 16#64 arena.upper).2.2.1
    omega
  have wider : next.Regions nodeLower (PersistentAlloc.rounded heap 16#64).toNat:=by
    intro node live active
    obtain ⟨floor,bounds,aligned,before⟩:=nextRegions node live active
    exact ⟨floor,bounds,aligned,before.trans grows⟩
  have cells:=post_cells source heap root flag arena
  exact ⟨fields,next,same,wider,nextDisjoint,nextValues,nextPaths,
    nextPathRegions.weaken next pathLower heap.toNat pathLower (PersistentAlloc.rounded heap 16#64).toNat (Nat.le_refl _) grows,
    nextSeparated,⟨arena,aligned,cells.1,cells.2,by rw [same]; exact member,
      rootSafe.of_fields graph next heap same fields,flagSafe.of_fields graph next (heap+8#64) same fields⟩⟩

end InitECandidate.Solver.Mpt.NewTrie

#print axioms InitECandidate.Solver.Mpt.NewTrie.post_graph
