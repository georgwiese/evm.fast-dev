import InitECandidate.Solver.Mpt.TriePathBuffer
import InitECandidate.Solver.Mpt.TrieGraphCacheOffsets

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

theorem Graph.Regions.footprint_before {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper)
    (query : BitVec 64) (required : graph.Footprint query) : query.toNat<upper := by
  obtain ⟨node,offset,member,active,inside,data,equal⟩:=required.data_location graph query
  have bounds:=regions node member active
  rw [equal,byteAddress_toNat node offset (by have bound:=bounds.2.1.upper; omega)]
  omega

/-- After a real split, retained old nodes still protect their full path.
The older-memory frame identifies its original pointer and length, so an
optional new extension may borrow a prefix even after new nodes were added. -/
theorem Graph.PathBuffer.old_stored_prefix (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (next : Graph target.memory target.memaddrs)
    (nodeLower oldUpper pathLower nextUpper : Nat) (regions : graph.Regions nodeLower oldUpper)
    (paths : next.PathBytes target.be) (pathRegions : next.PathRegions pathLower nextUpper) (separated : next.PathSeparated)
    (node prefixLength : BitVec 64) (member : graph.valid node) (active : node≠0#64)
    (tag : wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64) (nextMember : next.valid node)
    (bound : prefixLength.toNat≤(wordAt source.memory (node+40#64)).toNat)
    (olderMemory : ∀ query : BitVec 64,query.toNat<oldUpper → target.memory query=source.memory query) :
    next.PathBuffer target.be pathLower nextUpper (wordAt source.memory (node+32#64)) prefixLength.toNat := by
  have tagEq : wordAt target.memory node=wordAt source.memory node:=by
    unfold wordAt
    rw [olderMemory node (regions.footprint_before graph nodeLower oldUpper node (.header node member active))]
  have pointerEq : wordAt target.memory (node+32#64)=wordAt source.memory (node+32#64):=by
    unfold wordAt
    rw [olderMemory (node+32#64) (regions.footprint_before graph nodeLower oldUpper (node+32#64) (.pointer node member active tag))]
  have sizeEq : wordAt target.memory (node+40#64)=wordAt source.memory (node+40#64):=by
    unfold wordAt
    rw [olderMemory (node+40#64) (regions.footprint_before graph nodeLower oldUpper (node+40#64) (.size node member active tag))]
  have currentTag : wordAt target.memory node=1#64 ∨ wordAt target.memory node=2#64:=by rwa [tagEq]
  have stored:=Graph.PathBuffer.stored next target.be pathLower nextUpper paths pathRegions separated node nextMember active currentTag
  have currentBound : prefixLength.toNat≤(wordAt target.memory (node+40#64)).toNat:=by rw [sizeEq]; exact bound
  have window:=stored.window next target.be pathLower nextUpper (wordAt target.memory (node+32#64)) 0#64 (wordAt target.memory (node+40#64)).toNat prefixLength.toNat (by change 0≤_; omega)
    (by simpa only [show (0#64 : BitVec 64).toNat=0 from rfl,Nat.sub_zero] using currentBound)
  simpa only [BitVec.add_zero,pointerEq] using window

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.Regions.footprint_before
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBuffer.old_stored_prefix
