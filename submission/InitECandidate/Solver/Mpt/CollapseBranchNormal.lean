import InitECandidate.Solver.Mpt.CollapseBranchChoicesNormal
import InitECandidate.Solver.Mpt.CollapseBranchScanEntry
import InitECandidate.Solver.Mpt.CollapseBranchValueEntry
import InitECandidate.Solver.Mpt.TrieGraphPathErase

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole unchanged252 normal graph contract, derived through the actual
scan, stored value, all collapse choices, helper calls and lexical exits.
Only the real returned node can enlarge the registry, and every word below
the incoming heap remains unchanged. No future graph success is assumed. -/
theorem body_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap node : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (floor : 2701131776≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=3#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      ∃ root finalHeap : BitVec 64,value=.val (.word root) ∧ target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧ (graph.valid root ∨ heap.toNat≤root.toNat) ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ current,next.valid current ↔ graph.valid current ∨ current=root) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated := by
  have children (index : Nat) (inside : index<16) : ∃ child : BitVec 64,source.memaddrs (node+32#64+BitVec.ofNat 64 index*8#64) ∧
      source.memory (node+32#64+BitVec.ofNat 64 index*8#64)=.word child:=by
    let view:=graph.branch node member active (by rw [tag]; decide) (by rw [tag]; decide) (by rw [tag]; decide) index inside
    have product : BitVec.ofNat 64 (index*8)=BitVec.ofNat 64 index*8#64:=by rw [BitVec.ofNat_mul]
    exact ⟨view.child,by simpa only [product] using view.mapped,by simpa only [product] using view.stored⟩
  obtain ⟨scanned,inner,finished,_scanRun,_stopped,scannerFrame,continued,_clock,frame⟩:=scan_entry source target node nodeCell children value normal
  obtain ⟨current,same,currentRegions,currentDisjoint,⟨currentValues⟩,currentPaths,currentPathRegions,currentSeparated⟩:=
    graph.after_erase source scanned limit nodeLower heap.toNat pathLower heap.toNat property values regions disjoint paths pathRegions separated scannerFrame
  have scannerMemory:=Input.LocalEffects.memory_of_erase source scanned scannerFrame
  have scannerGlobals:=congrArg PanSemStateFiniteExact.globals scannerFrame
  have scannerDomain:=congrArg PanSemStateFiniteExact.memaddrs scannerFrame
  have scannerEndian:=congrArg PanSemStateFiniteExact.be scannerFrame
  have scannerCode:=congrArg PanSemStateFiniteExact.code scannerFrame
  change scanned.globals=source.globals at scannerGlobals
  change scanned.memaddrs=source.memaddrs at scannerDomain
  change scanned.be=source.be at scannerEndian
  change scanned.code=source.code at scannerCode
  have currentMember : current.valid node:=by rw [same]; exact member
  have currentTag : wordAt scanned.memory node=3#64:=by rw [scannerMemory]; exact tag
  have currentHeapCell : scanned.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [scannerGlobals]; exact heapCell
  have currentInstalled : Input.OriginalCode.Installed scanned.code:=by rw [scannerCode]; exact installed
  obtain ⟨valueInner,valueRun,innerEq⟩:=value_entry_normal scanned inner node current limit property currentValues currentMember active currentTag finished.nodeCell value continued
  let valueState:=QueryBranch.bind scanned "vl" (wordAt scanned.memory (node+168#64))
  let valueModel:=finished.with_value scanned node (wordAt scanned.memory (node+168#64))
  have valueCell : valueState.locals.lookup (ofString "vl")=some (.val (.word (wordAt valueState.memory (node+168#64)))):=bind_lookup_same _ _ _
  obtain ⟨_domainEq,_endianEq,_codeEq,older,root,finalHeap,answer,finalCell,finalArena,finalAligned,grows,fresh,
    result,members,rootMember,resultRegions,resultDisjoint,⟨resultValues⟩,resultPaths,resultPathRegions,resultSeparated⟩:=
    choices_paths valueState valueInner heap node valueModel current limit nodeLower pathLower property currentValues currentRegions currentDisjoint currentPaths currentPathRegions currentSeparated
      floor pathFloor nodeFloor currentMember active currentTag valueCell currentHeapCell frontier aligned (scannerEndian.trans little) (scannerDomain.trans domain) currentInstalled value valueRun
  rw [innerEq] at frame
  change Input.LocalEffects.erase target=Input.LocalEffects.erase valueInner at frame
  have finalMemory:=Input.LocalEffects.memory_of_erase valueInner target frame
  have finalGlobals:=congrArg PanSemStateFiniteExact.globals frame
  change target.globals=valueInner.globals at finalGlobals
  obtain ⟨next,finalSame,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    result.after_erase valueInner target limit nodeLower finalHeap.toNat pathLower finalHeap.toNat property resultValues resultRegions resultDisjoint resultPaths resultPathRegions resultSeparated frame
  have finalHeapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)):=by rw [finalGlobals]; exact finalCell
  have finalFresh : graph.valid root ∨ heap.toNat≤root.toNat:=by rw [same] at fresh; exact fresh
  have exactMembers (currentNode : BitVec 64) : next.valid currentNode ↔ graph.valid currentNode ∨ currentNode=root:=by rw [finalSame,members currentNode,same]
  have olderMemory (query : BitVec 64) (before : query.toNat<heap.toNat) : target.memory query=source.memory query:=
    (congrFun finalMemory query).trans ((older query before).trans (congrFun scannerMemory query))
  have fields:=Input.evaluation_fields source target body (some (.returned value)) normal
  exact ⟨fields.1,fields.2.1,fields.2.2.2,olderMemory,root,finalHeap,answer,finalHeapCell,finalArena,finalAligned,grows,finalFresh,next,exactMembers,
    (by rw [finalSame]; exact rootMember),nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.body_path_normal
