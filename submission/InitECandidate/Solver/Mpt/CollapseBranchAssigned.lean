import InitECandidate.Solver.Mpt.CollapseBranchNormal
import InitECandidate.Solver.Mpt.CollapseBranchCost
import InitECandidate.Solver.Mpt.DeleteHelperGlobals
import InitECandidate.Solver.Mpt.TrieGraphPathFieldsFrame
import InitECandidate.Solver.Input.AssignedCallKnown

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real assigned original252 caller retains the physical graph,
saved parent descriptors, all older memory and every nonheap global.
The local source allowance uses a present physical path extent. -/
theorem assigned_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap node : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (floor : 2701131776≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=3#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (name : MlS) (arguments : List (ExpHOL 64))
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word node)])
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "_collapse_branch") arguments)=(none,target)) :
    ∃ root : BitVec 64,target.locals=source.locals.update (name,.val (.word root)) ∧
      target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      source.clock-target.clock≤(heap.toNat-pathLower)/8+40 ∧
      (∀ key,key≠ofString "heap_ptr"→target.globals.lookup key=source.globals.lookup key) ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat→target.memory query=source.memory query) ∧ graph.PathFields target.memory ∧
      ∃ finalHeap : BitVec 64,target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧ (graph.valid root ∨ heap.toNat≤root.toNat) ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ current,next.valid current ↔ graph.valid current ∨ current=root) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated := by
  obtain ⟨callee,called,nodeCell⟩:=environment source node (original_code source.code installed)
  obtain ⟨funded,childTarget,returned,run,endpoint⟩:=Input.CallNormal.local_known source target name (ofString "_collapse_branch") arguments _ body callee .one argsRead called normal
  obtain ⟨domainEq,endianEq,codeEq,older,root,finalHeap,answer,finalCell,finalArena,finalAligned,grows,fresh,
    next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    body_path_normal (callEntryStateHOLFinite source callee) childTarget heap node graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated
      floor pathFloor nodeFloor member active tag nodeCell heapCell frontier aligned little domain installed returned run
  have priced:=body_cost (callEntryStateHOLFinite source callee) heap node graph limit nodeLower pathLower (heap.toNat-pathLower) property values regions disjoint paths pathRegions separated
    (TrieWalk.Graph.PathLimit.of_regions graph pathLower heap.toNat pathRegions) (pathFloor.trans nodeFloor) floor member active tag nodeCell heapCell frontier aligned little domain installed
  rw [run] at priced
  change source.clock-1-childTarget.clock≤(heap.toNat-pathLower)/8+39 at priced
  have spent : source.clock-childTarget.clock≤(heap.toNat-pathLower)/8+40:=by omega
  have globalFrame (key : MlS) (other : key≠ofString "heap_ptr") : target.globals.lookup key=source.globals.lookup key:=by
    have frame:=Input.GlobalEffects.call_body key source.code (some (some name)) (ofString "_collapse_branch") arguments formals body .one
      (original_code source.code installed) (globals key source.code installed other) source rfl
    change Input.GlobalEffects.erase key (evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "_collapse_branch") arguments)).2=Input.GlobalEffects.erase key source at frame
    rw [normal] at frame
    exact congrArg Prod.snd frame
  have fields : graph.PathFields childTarget.memory:=TrieWalk.Graph.PathFields.of_prefix graph childTarget.memory nodeLower heap.toNat regions older
  rw [endpoint,answer] at globalFrame
  rw [endpoint,answer]
  exact ⟨root,rfl,domainEq,endianEq,codeEq,spent,globalFrame,older,fields,finalHeap,finalCell,finalArena,finalAligned,grows,fresh,
    next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.assigned_path_normal
