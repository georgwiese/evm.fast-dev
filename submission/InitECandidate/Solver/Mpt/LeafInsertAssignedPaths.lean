import InitECandidate.Solver.Mpt.InsertionHelperEnvironment
import InitECandidate.Solver.Mpt.LeafInsertNormal
import InitECandidate.Solver.Input.AssignedCallData

namespace InitECandidate.Solver.Mpt.InsertLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem assigned_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key length pointer size : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (member : graph.valid node) (active : node≠0#64) (leaf : wordAt source.memory node=1#64)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (small : length.toNat≤64) (name : MlS) (arguments : List (ExpHOL 64))
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (callValues node key length pointer size))
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "_insert_into_leaf") arguments)=(none,target)) :
    ∃ root : BitVec 64,target.locals=source.locals.update (name,.val (.word root)) ∧
      target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧ source.clock-target.clock≤5*length.toNat+243 ∧
      (∀ query : BitVec 64,query.toNat<nodeLower → target.memory query=source.memory query) ∧
      (∀ current,graph.valid current → current≠0#64 → wordAt target.memory current=wordAt source.memory current) ∧
      ∃ finalHeap : BitVec 64,target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ current,graph.valid current → next.valid current) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          graph.PathFields target.memory ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat → target.memory address=source.memory address) ∧
          (∀ current,next.valid current → graph.valid current ∨ heap.toNat≤current.toNat) ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat →
            TrieWalk.PathWordAway key length.toNat address → next.ProtectedWord address) := by
  obtain ⟨callee,expectedCall,nodeCell,keyCell,lengthCell,pointerCell,sizeCell⟩:=environment source node key length pointer size (original_code source.code installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,childTarget,returned,args,called,run,checked,endpoint⟩:=
    Input.CallNormal.local_data source target name (ofString "_insert_into_leaf") arguments normal
  have sameValues : actualValues=callValues node key length pointer size:=Option.some.inj (args.symm.trans argsRead)
  subst actualValues
  have same:=Option.some.inj (called.symm.trans expectedCall)
  have bodyEq:=congrArg Prod.fst same
  have mapEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  have shapeEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.2) same
  change actualBody=body at bodyEq
  change actualCallee=callee at mapEq
  change actualShape=.one at shapeEq
  subst actualBody
  subst actualCallee
  subst actualShape
  obtain ⟨domainEq,endianEq,codeEq,price,memory,tags,finalHeap,root,answer,finalHeapCell,finalArena,finalAligned,grows,next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,fields,protectedWords,provenance,protection⟩:=
    body_path_normal (callEntryStateHOLFinite source callee) childTarget heap node key length pointer size graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated
      query member active leaf nodeCell keyCell lengthCell pointerCell sizeCell payload extra floor empty domain heapCell frontier aligned installed small returned run
  have spent : source.clock-childTarget.clock≤5*length.toNat+243:=by
    change source.clock-1-childTarget.clock≤5*length.toNat+242 at price
    omega
  rw [endpoint,answer]
  exact ⟨root,rfl,domainEq,endianEq,codeEq,spent,memory,tags,finalHeap,finalHeapCell,finalArena,finalAligned,grows,
    next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,fields,protectedWords,provenance,protection⟩

end InitECandidate.Solver.Mpt.InsertLeaf

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.assigned_path_normal
