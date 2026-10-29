import InitECandidate.Solver.Mpt.NibbleKeyUnsecured
import InitECandidate.Solver.Mpt.TrieGraphPathPrefix
import InitECandidate.Solver.Mpt.TrieGraphPathFieldsFrame
import InitECandidate.Solver.PanHeapGlobals

namespace InitECandidate.Solver.Mpt.NibbleKey
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Actual unsecured conversion writes only its fresh nibble allocation.
Its established frame retains the old graph and derives a protected current
query, without any cryptographic oracle or later mutation premise. -/
theorem graph_after_unsecured_query (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (count : Nat) (small : count≤64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (pathFloor : pathLower≤heap.toNat) (arena : AllocatedBytes.Arena heap count) (aligned : heap.toNat%8=0)
    (view : TrieWalk.KeyView target.memory target.memaddrs target.be heap count)
    (frame : Input.MemoryMetadata.erase target=Input.MemoryMetadata.erase (PersistentAlloc.post source heap (BitVec.ofNat 64 count)))
    (memory : ∀ query : BitVec 64,query.toNat<heap.toNat→target.memory query=source.memory query) :
    let finalHeap:=PersistentAlloc.rounded heap (BitVec.ofNat 64 count)
    target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧ AllocatedBytes.Arena finalHeap 0 ∧
      finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧ HeapGlobals source target ∧ graph.PathFields target.memory ∧
      ∃ next : TrieWalk.Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
        next.PathBuffer target.be pathLower finalHeap.toNat heap count := by
  let amount:=BitVec.ofNat 64 count
  let finalHeap:=PersistentAlloc.rounded heap amount
  have amountNumber : amount.toNat=count:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have ordinaryRoom : heap.toNat+amount.toNat≤33806089496:=by rw [amountNumber]; exact arena.upper
  have number:=PersistentAlloc.rounded_nat heap amount (by omega)
  have endBefore : heap.toNat+count≤finalHeap.toNat:=by change heap.toNat+count≤(PersistentAlloc.rounded heap amount).toNat; rw [number]; omega
  have finalBound : finalHeap.toNat≤33806089496:=by change (PersistentAlloc.rounded heap amount).toNat≤33806089496; rw [number]; omega
  have finalAligned : finalHeap.toNat%8=0:=by change (PersistentAlloc.rounded heap amount).toNat%8=0; rw [number]; omega
  have grows : heap.toNat≤finalHeap.toNat:=by omega
  have nextArena : AllocatedBytes.Arena finalHeap 0:=⟨Nat.le_trans arena.lower grows,by omega⟩
  have domainEq:=Input.MemoryMetadata.domain frame
  change target.memaddrs=source.memaddrs at domainEq
  have endianEq:=Input.MemoryMetadata.endian frame
  change target.be=source.be at endianEq
  have globalsEq:=congrArg PanSemStateFiniteExact.globals frame
  change target.globals=(PersistentAlloc.post source heap amount).globals at globalsEq
  have heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)):=by
    rw [globalsEq]
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,finalHeap]
  have globals : HeapGlobals source target:=by
    intro name other
    rw [globalsEq]
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm other]
  obtain ⟨next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    graph.after_path_prefix source target limit nodeLower pathLower heap.toNat property values regions disjoint paths pathRegions separated domainEq endianEq memory
  have fields : graph.PathFields target.memory:=TrieWalk.Graph.PathFields.of_prefix graph target.memory nodeLower heap.toNat regions memory
  have enlargedRegions:=nextRegions.weaken next nodeLower heap.toNat nodeLower finalHeap.toNat (Nat.le_refl _) grows
  have enlargedPaths:=nextPathRegions.weaken next pathLower heap.toNat pathLower finalHeap.toNat (Nat.le_refl _) grows
  have fresh:=TrieWalk.Graph.PathBuffer.fresh next target.be nodeLower heap.toNat finalHeap.toNat heap count nextRegions aligned
    (view.nibble_span target.memory target.memaddrs target.be heap count) (Nat.le_refl _) endBefore
  have query : next.PathBuffer target.be pathLower finalHeap.toNat heap count:=⟨fresh.span,⟨pathFloor,fresh.bounds.2⟩,fresh.apart⟩
  exact ⟨heapCell,nextArena,finalAligned,grows,globals,fields,next,same,enlargedRegions,nextDisjoint,nextValues,nextPaths,enlargedPaths,nextSeparated,query⟩

end InitECandidate.Solver.Mpt.NibbleKey

#print axioms InitECandidate.Solver.Mpt.NibbleKey.graph_after_unsecured_query
