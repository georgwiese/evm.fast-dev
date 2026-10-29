import InitECandidate.Solver.Mpt.NodeConstructorCells
import InitECandidate.Solver.Input.AssignedCallData

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A genuine assigned scalar constructor call supplies its fresh node,
allocation and exact caller memory/heap update. Callee inputs come from
the real checked ABI; successful future allocation is not a premise. -/
theorem assigned_normal (kind : Kind) (scalar : kind≠.branch)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (words : String→BitVec 64)
    (name : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64)) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some values)
    (expectedCall : lookupCodeHOLFinite source.code.lookup (ofString (NodeConstructor.name kind)) values=some (body kind,callee,.one))
    (inputs : Inputs kind (callEntryStateHOLFinite source callee) words)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString (NodeConstructor.name kind)) arguments)=(none,target)) :
    AllocatedBytes.Arena heap (bytes kind) ∧ target=setVarHOLFinite name (.val (.word heap))
      {PersistentAlloc.post {source with clock:=source.clock-2} heap (BitVec.ofNat 64 (bytes kind)) with
        memory:=WordWrites.write source.memory (FieldStores.writes heap (fields kind words))} := by
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,childTarget,returned,args,called,run,checked,endpoint⟩:=
    Input.CallNormal.local_data source target name (ofString (NodeConstructor.name kind)) arguments normal
  have sameValues : actualValues=values:=Option.some.inj (args.symm.trans argsRead)
  subst actualValues
  have same:=Option.some.inj (called.symm.trans expectedCall)
  have bodyEq:=congrArg Prod.fst same
  have mapEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  have shapeEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.2) same
  change actualBody=body kind at bodyEq
  change actualCallee=callee at mapEq
  change actualShape=.one at shapeEq
  subst actualBody
  subst actualCallee
  subst actualShape
  obtain ⟨answer,arena,positive,frame⟩:=scalar_normal_from_arena kind scalar (callEntryStateHOLFinite source callee) childTarget heap words inputs domain
    heapCell frontier aligned installed returned run
  have restored:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  have callerEq : {childTarget with locals:=source.locals}=
      {PersistentAlloc.post {source with clock:=source.clock-2} heap (BitVec.ofNat 64 (bytes kind)) with
        memory:=WordWrites.write source.memory (FieldStores.writes heap (fields kind words))}:=by
    simpa only [callEntryStateHOLFinite,emptyLocalsHOLFinite,PersistentAlloc.post,Nat.sub_sub] using restored
  refine ⟨arena,?_⟩
  rw [endpoint,answer,callerEq]

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.assigned_normal
