import InitECandidate.Solver.Mpt.NibbleKeyGeneralCall
import InitECandidate.Solver.Mpt.TrieGraphPathBand
import InitECandidate.Solver.Mpt.TrieGraphPathFieldsFrame
import InitECandidate.Solver.Mpt.TrieGraphRegisteredRegions
import InitECandidate.Solver.Mpt.TriePathBuffer

namespace InitECandidate.Solver.Mpt.NibbleKey
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Hash stores and byte backing words cannot reach a query at or above
the actual workspace end. No alignment of the queried address is needed. -/
theorem workspace_away (pointer query : BitVec 64) (length cutoff : Nat)
    (before : pointer.toNat+length≤cutoff) (fits : cutoff<2^64) (above : cutoff≤query.toNat) : CopyGeneral.Away pointer query length := by
  intro offset inside
  have number:=byteAddress_toNat pointer offset (by omega)
  have backing : (panByteAlignHOL (width:=64) (byteAddress pointer offset)).toNat≤(byteAddress pointer offset).toNat:=by
    rw [AllocatedBytes.aligned_number]; omega
  constructor
  · intro same
    have equal:=congrArg BitVec.toNat same
    rw [number] at equal
    omega
  · intro same
    have equal:=congrArg BitVec.toNat same
    rw [number] at backing
    omega

/-- Reconstruct the real old trie and newly allocated protected query
from the actual key helper's established frame. All three hash workspaces
end below an aligned persistent cutoff, so both original secure flags
preserve complete old paths/values and every map-header word in that band. -/
theorem graph_after_query (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap stp pad hash : BitVec 64) (count : Nat) (small : count≤64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower cutoff : Nat) (property : BitVec 64→BitVec 64→Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (floor : cutoff≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat) (cutoffAligned : cutoff%8=0)
    (stateBefore : stp.toNat+200≤cutoff) (padBefore : pad.toNat+136≤cutoff) (hashBefore : hash.toNat+32≤cutoff)
    (arena : AllocatedBytes.Arena heap count) (heapAligned : heap.toNat%8=0)
    (view : TrieWalk.KeyView target.memory target.memaddrs target.be heap count)
    (frame : KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl (PersistentAlloc.post source heap (BitVec.ofNat 64 count)))
    (memory : ∀ query : BitVec 64,Keccak256.Protected stp pad hash query→
      (query.toNat<heap.toNat ∨ heap.toNat+count≤query.toNat)→target.memory query=source.memory query) :
    let finalHeap:=PersistentAlloc.rounded heap (BitVec.ofNat 64 count)
    target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧ AllocatedBytes.Arena finalHeap 0 ∧
      finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧ HeapGlobals source target ∧
      (∀ query : BitVec 64,cutoff≤query.toNat→query.toNat<heap.toNat→target.memory query=source.memory query) ∧
      graph.PathFields target.memory ∧
      ∃ next : TrieWalk.Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
        next.PathBuffer target.be pathLower finalHeap.toNat heap count := by
  let amount:=BitVec.ofNat 64 count
  let finalHeap:=PersistentAlloc.rounded heap amount
  have amountNumber : amount.toNat=count:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨_firstGuard,_secondGuard,endBefore,heapUpper,finalAligned⟩:=PersistentAlloc.guards heap amount (by simpa only [amountNumber] using arena.upper)
  have grows : heap.toNat≤finalHeap.toNat:=by change heap.toNat+amount.toNat≤finalHeap.toNat at endBefore; omega
  have nextArena : AllocatedBytes.Arena finalHeap 0:=⟨arena.lower.trans grows,by simpa only [Nat.add_zero] using heapUpper⟩
  have domainEq : target.memaddrs=source.memaddrs:=by have projected:=congrArg PanSemStateFiniteExact.memaddrs frame; exact projected
  have endianEq : target.be=source.be:=by have projected:=congrArg PanSemStateFiniteExact.be frame; exact projected
  have globalsEq : target.globals=(PersistentAlloc.post source heap amount).globals:=by have projected:=congrArg PanSemStateFiniteExact.globals frame; exact projected
  have heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)):=by
    rw [globalsEq]
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,finalHeap]
  have globals : HeapGlobals source target:=by
    intro name other
    rw [globalsEq]
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm other]
  have cutoffFits : cutoff<2^64:=by have upper:=arena.upper; omega
  have band (query : BitVec 64) (above : cutoff≤query.toNat) (before : query.toNat<heap.toNat) : target.memory query=source.memory query:=
    memory query ⟨workspace_away stp query 200 cutoff stateBefore cutoffFits above,workspace_away pad query 136 cutoff padBefore cutoffFits above,
      workspace_away hash query 32 cutoff hashBefore cutoffFits above⟩ (Or.inl before)
  obtain ⟨next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=graph.after_path_band source target limit nodeLower pathLower heap.toNat cutoff property
    values regions disjoint paths pathRegions separated cutoffAligned (floor.trans pathFloor) floor domainEq endianEq band
  have fields : graph.PathFields target.memory:=TrieWalk.Graph.PathFields.of_agreement graph target.memory (by
    intro query required
    have bounds:=graph.footprint_bounds nodeLower heap.toNat regions query required
    exact band query ((floor.trans pathFloor).trans bounds.1) bounds.2)
  have enlargedRegions:=nextRegions.weaken next nodeLower heap.toNat nodeLower finalHeap.toNat (Nat.le_refl _) grows
  have enlargedPaths:=nextPathRegions.weaken next pathLower heap.toNat pathLower finalHeap.toNat (Nat.le_refl _) grows
  have fresh:=TrieWalk.Graph.PathBuffer.fresh next target.be nodeLower heap.toNat finalHeap.toNat heap count nextRegions heapAligned
    (view.nibble_span target.memory target.memaddrs target.be heap count) (Nat.le_refl _) (by simpa only [amountNumber] using endBefore)
  have query : next.PathBuffer target.be pathLower finalHeap.toNat heap count:=⟨fresh.span,⟨pathFloor.trans nodeFloor,fresh.bounds.2⟩,fresh.apart⟩
  exact ⟨heapCell,nextArena,finalAligned,grows,globals,band,fields,next,same,enlargedRegions,nextDisjoint,nextValues,nextPaths,enlargedPaths,nextSeparated,query⟩

end InitECandidate.Solver.Mpt.NibbleKey

#print axioms InitECandidate.Solver.Mpt.NibbleKey.workspace_away
#print axioms InitECandidate.Solver.Mpt.NibbleKey.graph_after_query
