import InitECandidate.Solver.Mpt.DeleteExtensionNormal
import InitECandidate.Solver.Mpt.DeleteHelperGlobals
import InitECandidate.Solver.Input.AssignedCallKnown

namespace InitECandidate.Solver.Mpt.DeleteExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The genuine four-word assigned original253 call, retaining the real
result, current graph, saved parent fields and both low arena cursors. -/
theorem assigned_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap node child segment length : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (segmentBuffer : graph.PathBuffer source.be pathLower heap.toNat segment length.toNat) (floor : 2701131776≤pathLower)
    (nodeFloor : nodeLower≤heap.toNat) (positive : 0<length.toNat)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=2#64) (childMember : graph.valid child)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (name : MlS) (arguments : List (ExpHOL 64))
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word node),.val (.word segment),.val (.word length),.val (.word child)])
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "_delete_ext_finish") arguments)=(none,target)) :
    ∃ root : BitVec 64,target.locals=source.locals.update (name,.val (.word root)) ∧
      target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      source.clock-target.clock≤length.toNat/8+(wordAt source.memory (child+40#64)).toNat/8+23 ∧
      (∀ key,key≠ofString "heap_ptr"→target.globals.lookup key=source.globals.lookup key) ∧
      (∀ query : BitVec 64,query.toNat<nodeLower→target.memory query=source.memory query) ∧ graph.PathFields target.memory ∧
      ∃ finalHeap : BitVec 64,target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧ (graph.valid root ∨ heap.toNat≤root.toNat) ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ current,next.valid current ↔ graph.valid current ∨ current=root) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated := by
  obtain ⟨callee,called,nodeCell,segmentCell,lengthCell,childCell⟩:=Input.word_quad_environment source.code.lookup (ofString "_delete_ext_finish")
    (ofString "node") (ofString "seg") (ofString "sl") (ofString "nc") body .one node segment length child
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (original_code source.code installed)
  obtain ⟨funded,childTarget,returned,run,endpoint⟩:=Input.CallNormal.local_known source target name (ofString "_delete_ext_finish") arguments _ body callee .one argsRead called normal
  obtain ⟨domainEq,endianEq,codeEq,price,older,fields,root,finalHeap,answer,finalCell,finalArena,finalAligned,grows,fresh,
    next,_included,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    body_path_normal (callEntryStateHOLFinite source callee) childTarget heap node child segment length graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated
      segmentBuffer floor nodeFloor positive member active tag childMember nodeCell segmentCell lengthCell childCell heapCell frontier aligned little domain installed returned run
  have spent : source.clock-childTarget.clock≤length.toNat/8+(wordAt source.memory (child+40#64)).toNat/8+23:=by
    change source.clock-1-childTarget.clock≤length.toNat/8+(wordAt source.memory (child+40#64)).toNat/8+22 at price
    omega
  have globalFrame (key : MlS) (other : key≠ofString "heap_ptr") : target.globals.lookup key=source.globals.lookup key:=by
    have frame:=Input.GlobalEffects.call_body key source.code (some (some name)) (ofString "_delete_ext_finish") arguments formals body .one
      (original_code source.code installed) (globals key source.code installed other) source rfl
    change Input.GlobalEffects.erase key (evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "_delete_ext_finish") arguments)).2=Input.GlobalEffects.erase key source at frame
    rw [normal] at frame
    exact congrArg Prod.snd frame
  rw [endpoint,answer] at globalFrame
  rw [endpoint,answer]
  exact ⟨root,rfl,domainEq,endianEq,codeEq,spent,globalFrame,older,fields,finalHeap,finalCell,finalArena,finalAligned,grows,fresh,
    next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩

end InitECandidate.Solver.Mpt.DeleteExtension

#print axioms InitECandidate.Solver.Mpt.DeleteExtension.assigned_path_normal
