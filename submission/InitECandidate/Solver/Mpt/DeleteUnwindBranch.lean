import InitECandidate.Solver.Mpt.DeleteUnwindChildStore
import InitECandidate.Solver.Mpt.DeleteUnwindOutput
import InitECandidate.Solver.Mpt.CollapseBranchAssigned

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual branch unwind first replaces its true saved child slot,
then collapses that same physical parent through original252. The resulting
registry and parent frames are derived from both genuine operations. -/
theorem unwind_branch_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (saved : DeleteFrame.Saved) (result heap : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (view : saved.View source) (owned : saved.Owned graph) (branchKind : saved.kind=.branch)
    (resultMember : graph.valid result) (floor : 2701131776≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word saved.pointer)))
    (nodeCell : source.locals.lookup (ofString "fnode")=some (.val (.word saved.node)))
    (resultCell : source.locals.lookup (ofString "res")=some (.val (.word result)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source unwindChoice=(none,target)) :
    Nonempty (ChoiceOutput source target graph heap limit nodeLower pathLower property) := by
  obtain ⟨executed,storeMemory,storeFields,current,same,currentRegions,currentDisjoint,⟨currentValues⟩,currentPaths,currentPathRegions,currentSeparated⟩:=
    branch_child_store source saved result graph limit nodeLower heap.toNat pathLower property values regions disjoint paths pathRegions separated
      view owned branchKind resultMember topCell nodeCell resultCell domain
  let post:=branchPost source saved result
  rw [unwind_dispatch source saved view domain topCell,branchKind,branchUnwind,
    StateSteps.next_sequence source post replaceChild finishBranch executed (Nat.le_refl _)] at normal
  have args : evalListHOLFinite post (h:=fun query=>Classical.propDecidable (post.memaddrs query)) branchArguments=some [.val (.word saved.node)]:=by
    simp [branchArguments,evalListHOLFinite,evalListHOLExact,localVar,evalHOLExact,toExact,show post.locals.lookup (ofString "fnode")=some (.val (.word saved.node)) from nodeCell]
  have currentMember : current.valid saved.node:=by rw [same]; exact owned.1
  have tag : wordAt source.memory saved.node=3#64:=by simpa only [branchKind,DeleteFrame.Kind.tag] using owned.2.2.1
  have currentTag : wordAt post.memory saved.node=3#64:=(storeFields.tags saved.node owned.1 owned.2.1).trans tag
  obtain ⟨root,localsEq,domainEq,endianEq,codeEq,_price,globalsEq,helperMemory,helperFields,finalHeap,finalCell,finalArena,finalAligned,grows,fresh,
    next,members,rootMember,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated⟩:=
    CollapseBranch.assigned_path_normal post target heap saved.node current limit nodeLower pathLower property currentValues currentRegions currentDisjoint currentPaths currentPathRegions currentSeparated
      floor pathFloor nodeFloor currentMember owned.2.1 currentTag heapCell frontier aligned little domain installed (ofString "res") branchArguments args normal
  have older (query : BitVec 64) (before : query.toNat<nodeLower) : target.memory query=source.memory query:=
    (helperMemory query (by omega)).trans (storeMemory query before)
  have fields : graph.PathFields target.memory:=storeFields.trans graph current helperFields (by intro node member; rw [same]; exact member)
  have exactMembers (node : BitVec 64) : next.valid node ↔ graph.valid node ∨ node=root:=by rw [members node,same]
  have sourceFresh : graph.valid root ∨ heap.toNat≤root.toNat:=by
    rcases fresh with old|above
    · exact Or.inl (by rwa [same] at old)
    · exact Or.inr above
  exact ⟨⟨root,finalHeap,localsEq,domainEq,endianEq,codeEq,globalsEq,older,fields,finalCell,finalArena,finalAligned,grows,sourceFresh,
    next,exactMembers,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.unwind_branch_normal
