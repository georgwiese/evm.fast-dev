import InitECandidate.Solver.Mpt.InsertEmptyGraph
import InitECandidate.Solver.Mpt.InsertEnvironment
import InitECandidate.Solver.Input.AssignedCallData

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The real assigned empty-insertion caller receives the newly allocated
leaf and its full physical graph/value model. All callee ABI fields and
allocation facts are derived from this actual call and normal return. -/
theorem empty_assigned_graph (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap key length pointer size : BitVec 64) (name : MlS) (arguments : List (ExpHOL 64))
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some (values 0#64 key length 0#64 pointer size))
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (fits : key.toNat+min length.toNat 64<2^64)
    (mapped : ∀ offset<min length.toNat 64,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress key offset)))
    (limit : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "_mpt_insert_node") arguments)=(none,target)) :
    AllocatedBytes.Arena heap 64 ∧ target.locals.lookup name=some (.val (.word heap)) ∧ source.clock-target.clock≤4 ∧
      target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 64#64))) ∧
      AllocatedBytes.Arena (PersistentAlloc.rounded heap 64#64) 0 ∧ (PersistentAlloc.rounded heap 64#64).toNat%8=0 ∧
      heap.toNat+64≤(PersistentAlloc.rounded heap 64#64).toNat ∧
      ∃ graph : TrieWalk.Graph target.memory target.memaddrs,
        (∀ node,graph.valid node ↔ node=0#64 ∨ node=heap) ∧ graph.valid heap ∧
        graph.Regions heap.toNat (PersistentAlloc.rounded heap 64#64).toNat ∧ graph.Disjoint ∧
        Nonempty (TrieWalk.Values graph limit property) := by
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,child,returned,args,called,run,checked,endpoint⟩:=
    Input.CallNormal.local_data source target name (ofString "_mpt_insert_node") arguments normal
  have sameValues : actualValues=values 0#64 key length 0#64 pointer size:=Option.some.inj (args.symm.trans argsRead)
  subst actualValues
  obtain ⟨callee,expectedCall,nodeCell,keyCell,lengthCell,levelCell,pointerCell,sizeCell⟩:=
    environment source.code.lookup 0#64 key length 0#64 pointer size (original_code source.code installed)
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
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨arena,answer,cost,globals,nextArena,nextAligned,before,cells,oldMemory⟩:=
    empty_physical entry child heap key length pointer size nodeCell keyCell lengthCell levelCell pointerCell sizeCell
      installed domain heapCell frontier aligned returned run
  obtain ⟨_,_,graph,valid,member,regions,disjoint,values⟩:=
    empty_graph entry child heap key length pointer size nodeCell keyCell lengthCell levelCell pointerCell sizeCell
      installed domain heapCell frontier aligned fits mapped limit property payload extra returned run
  refine ⟨arena,?_,?_,?_,nextArena,nextAligned,before,?_⟩
  · rw [endpoint,answer]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · have finalClock : target.clock=child.clock:=by rw [endpoint]; rfl
    rw [finalClock]
    change source.clock-1-child.clock≤3 at cost
    omega
  · rw [endpoint]
    exact globals
  · rw [endpoint]
    exact ⟨graph,valid,member,regions,disjoint,values⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.empty_assigned_graph
