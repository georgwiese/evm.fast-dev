import InitECandidate.Solver.Mpt.LeafInsertBranchEntry
import InitECandidate.Solver.Mpt.LeafInsertAfterBranch

namespace InitECandidate.Solver.Mpt.InsertLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete original249 suffix after its bounded prefix comparison:
the actual248 call, optional extension tail call and both caller scopes. -/
theorem after_prefix_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key length pointer size prefixLength : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (member : graph.valid node) (active : node≠0#64) (leaf : wordAt source.memory node=1#64)
    (bound : prefixLength.toNat≤min (wordAt source.memory (node+40#64)).toNat length.toNat)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (leftCell : source.locals.lookup (ofString "ek")=some (.val (.word (wordAt source.memory (node+32#64)))))
    (oldLengthCell : source.locals.lookup (ofString "el")=some (.val (.word (wordAt source.memory (node+40#64)))))
    (keyCell : source.locals.lookup (ofString "rk")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "rl")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterPrefix=(some (.returned value),target)) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧ source.clock-target.clock≤239 ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      ∃ finalHeap root : BitVec 64,value=.val (.word root) ∧ target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ current,graph.valid current → next.valid current) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          (∀ current,next.valid current → graph.valid current ∨ heap.toNat≤current.toNat) ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat →
            TrieWalk.PathWordAway key length.toNat address → next.ProtectedWord address) ∧ TrieWalk.Uncached target.memory root := by
  obtain ⟨ready,inner,branchCell,localsEq,domainEq,endianEq,codeEq,price,continued,endpoint,olderMemory,currentHeap,currentHeapCell,currentArena,currentAligned,grows,branchTag,base,oldMember,branchMember,baseRegions,baseDisjoint,⟨baseValues⟩,basePaths,basePathRegions,baseSeparated,buffer,baseFresh,baseProtection,branchClean⟩:=
    branch_entry_normal source target heap node key length pointer size prefixLength graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated query member active leaf bound
      nodeCell leftCell oldLengthCell keyCell lengthCell pointerCell sizeCell prefixCell payload extra floor empty domain heapCell frontier aligned installed value normal
  have currentKey : ready.locals.lookup (ofString "ek")=some (.val (.word (wordAt source.memory (node+32#64)))):=by
    rw [localsEq]
    simpa [HolFiniteMapExact.update,FUPDATE,ofString] using leftCell
  have currentPrefix : ready.locals.lookup (ofString "pl")=some (.val (.word prefixLength)):=by
    rw [localsEq]
    simpa [HolFiniteMapExact.update,FUPDATE,ofString] using prefixCell
  have readyInstalled : Input.OriginalCode.Installed ready.code:=by rw [codeEq]; exact installed
  obtain ⟨finalDomain,finalEndian,finalCode,finalPrice,finalMemory,finalHeap,root,answer,finalHeapCell,finalArena,finalAligned,finalGrows,next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,finalFresh,finalProtection,rootClean⟩:=
    after_branch_normal ready inner currentHeap (wordAt source.memory (node+32#64)) prefixLength heap base limit nodeLower pathLower property baseValues baseRegions baseDisjoint basePaths basePathRegions baseSeparated
      buffer branchMember (floor.trans grows) currentKey currentPrefix branchCell (domainEq.trans domain) currentHeapCell currentArena currentAligned readyInstalled value continued
  have spent : source.clock-inner.clock≤239:=by omega
  have memory (query : BitVec 64) (before : query.toNat<heap.toNat) : inner.memory query=source.memory query:=
    (finalMemory query (before.trans_le grows)).trans (olderMemory query before)
  have inclusion (current : BitVec 64) (live : graph.valid current) : next.valid current:=members current (oldMember current live)
  have provenance (current : BitVec 64) (live : next.valid current) : graph.valid current ∨ heap.toNat≤current.toNat:=by
    rcases finalFresh current live with old|fresh
    · exact baseFresh current old
    · exact Or.inr (grows.trans fresh)
  have protection (address : BitVec 64) (safe : graph.ProtectedWord address) (before : address.toNat<heap.toNat)
      (away : TrieWalk.PathWordAway key length.toNat address) : next.ProtectedWord address:=by
    have baseSafe:=baseProtection address safe before away
    have oldAway:=safe.stored graph address node member active (Or.inl leaf)
    have prefixBound : prefixLength.toNat≤(wordAt source.memory (node+40#64)).toNat:=bound.trans (Nat.min_le_left _ _)
    have leading:=oldAway.window _ 0#64 address _ prefixLength.toNat (by change 0≤(wordAt source.memory (node+40#64)).toNat; omega)
      (by change prefixLength.toNat≤(wordAt source.memory (node+40#64)).toNat; exact prefixBound)
    exact finalProtection address baseSafe (before.trans_le grows) (by simpa only [BitVec.add_zero] using leading)
  rw [endpoint]
  exact ⟨finalDomain.trans domainEq,finalEndian.trans endianEq,finalCode.trans codeEq,spent,memory,finalHeap,root,answer,
    finalHeapCell,finalArena,finalAligned,grows.trans finalGrows,next,inclusion,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,provenance,protection,rootClean branchClean⟩

end InitECandidate.Solver.Mpt.InsertLeaf

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.after_prefix_path_normal
