import InitECandidate.Solver.Mpt.SplitExtensionAfterBranch
import InitECandidate.Solver.Mpt.SplitExtensionBranchEntry

namespace InitECandidate.Solver.Mpt.SplitExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem branch_scope_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap segment prefixLength oldLength child key length pointer size : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat segment oldLength.toNat)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (queryBound : prefixLength.toNat≤length.toNat)
    (keyCell : source.locals.lookup (ofString "rk")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "rl")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (strict : prefixLength.toNat<oldLength.toNat) (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64)
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (oldLengthCell : source.locals.lookup (ofString "sl")=some (.val (.word oldLength)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (childMember : graph.valid child)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source branchScope=(some (.returned value),target)) :
    value=.val (.word heap) ∧ target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      ∃ finalHeap : BitVec 64,target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧ wordAt target.memory heap=3#64 ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,
          (∀ node,graph.valid node → next.valid node) ∧ next.valid heap ∧ next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧
          Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          (∀ current,next.valid current → graph.valid current ∨ heap.toNat≤current.toNat) ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat →
            TrieWalk.PathWordAway segment oldLength.toNat address → TrieWalk.PathWordAway key length.toNat address → next.ProtectedWord address) := by
  obtain ⟨ready,inner,branchCell,localsEq,physical,codeEq,continued,endpoint,base,members,member,baseRegions,baseDisjoint,⟨baseValues⟩,basePaths,basePathRegions,baseSeparated,first,other⟩:=
    branch_entry source target heap segment oldLength key length graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated buffer query
      floor empty domain heapCell frontier aligned installed value normal
  have branchActive : heap≠0#64:=by
    intro zero
    have lower:=frontier.lower
    rw [zero] at lower
    change 2701131776≤0 at lower
    omega
  have currentTag : wordAt ready.memory heap=3#64:=by simp [wordAt,physical.tag,MemoryBytes.wordBits]
  have grows : heap.toNat≤(PersistentAlloc.rounded heap 176#64).toNat:=by
    have before : heap.toNat+176≤(PersistentAlloc.rounded heap 176#64).toNat:=physical.allocation.before
    omega
  have currentInstalled : Input.OriginalCode.Installed ready.code:=by rw [codeEq]; exact installed
  have current (name : MlS) (other : name≠ofString "br") : ready.locals.lookup name=source.locals.lookup name:=by
    rw [localsEq]
    simp [HolFiniteMapExact.update,FUPDATE,Ne.symm other]
  obtain ⟨answer,domainEq,endianEq,finalCode,memory,finalHeap,finalHeapCell,finalArena,finalAligned,finalGrows,finalTag,next,oldMembers,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,finalFresh,finalProtection⟩:=
    after_branch_normal ready inner (PersistentAlloc.rounded heap 176#64) heap segment prefixLength oldLength child key length pointer size
      base limit nodeLower pathLower property baseValues baseRegions baseDisjoint basePaths basePathRegions baseSeparated first other queryBound
      ((current _ (by decide)).trans keyCell) ((current _ (by decide)).trans lengthCell) ((current _ (by decide)).trans pointerCell) ((current _ (by decide)).trans sizeCell)
      (by rw [physical.allocation.domain]; exact payload) extra strict (floor.trans grows) branchCell
      ((current _ (by decide)).trans segmentCell) ((current _ (by decide)).trans prefixCell) ((current _ (by decide)).trans oldLengthCell) ((current _ (by decide)).trans childCell)
      member branchActive currentTag ((members child).mpr (Or.inl childMember)) (physical.allocation.domain.trans domain)
      physical.allocation.heapCell physical.allocation.nextArena physical.allocation.nextAligned currentInstalled value continued
  have prefixMemory (query : BitVec 64) (before : query.toNat<heap.toNat) : inner.memory query=source.memory query:=
    (memory query before).trans (physical.allocation.memory query (Or.inl before))
  have inclusion (node : BitVec 64) (live : graph.valid node) : next.valid node:=oldMembers node ((members node).mpr (Or.inl live))
  have provenance (current : BitVec 64) (live : next.valid current) : graph.valid current ∨ heap.toNat≤current.toNat:=by
    rcases finalFresh current live with old|fresh
    · rcases (members current).mp old with original|branch
      · exact Or.inl original
      · exact Or.inr (by rw [branch])
    · exact Or.inr (grows.trans fresh)
  have protection (address : BitVec 64) (safe : graph.ProtectedWord address) (before : address.toNat<heap.toNat)
      (oldAway : TrieWalk.PathWordAway segment oldLength.toNat address) (queryAway : TrieWalk.PathWordAway key length.toNat address) : next.ProtectedWord address:=by
    have baseSafe:=(physical.protected source ready heap graph base nodeLower regions members address safe before).2
    exact finalProtection address baseSafe (before.trans_le grows) oldAway queryAway
  rw [endpoint]
  exact ⟨answer,domainEq.trans physical.allocation.domain,endianEq.trans physical.allocation.endian,finalCode.trans codeEq,prefixMemory,
    finalHeap,finalHeapCell,finalArena,finalAligned,grows.trans finalGrows,finalTag,next,inclusion,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,provenance,protection⟩

end InitECandidate.Solver.Mpt.SplitExtension

#print axioms InitECandidate.Solver.Mpt.SplitExtension.branch_scope_normal
