import InitECandidate.Solver.Mpt.NodeConstructorScoped
import InitECandidate.Solver.Input.ScopedCallNone

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Follow the real scoped scalar call into its actual caller continuation
with the physical allocation contract and genuine result binding. -/
theorem scalar_scoped_none_physical (kind : Kind) (scalar : kind≠.branch)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (words : String → BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64)) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (continuation : ProgHOL 64)
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some values)
    (expectedCall : lookupCodeHOLFinite source.code.lookup (ofString (NodeConstructor.name kind)) values=some (body kind,callee,.one))
    (inputs : Inputs kind (callEntryStateHOLFinite source callee) words)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString (NodeConstructor.name kind)) arguments continuation)=(none,post)) :
    1≤source.clock ∧ ∃ ready inner,
      ready.locals.lookup (ofString name)=some (.val (.word heap)) ∧ ready.locals=source.locals.update (ofString name,.val (.word heap)) ∧ Physical kind source ready heap words ∧ ready.code=source.code ∧
      evaluateHOLFiniteState ready continuation=(none,inner) ∧ post=QueryBranch.restore source name inner := by
  obtain ⟨funded,target,returned,inner,run,checked,continued,endpoint⟩:=Input.CallNormal.scoped_none source post name .one
    (ofString (NodeConstructor.name kind)) arguments values (body kind) continuation callee .one argsRead expectedCall normal
  obtain ⟨answer,physical⟩:=scalar_physical kind scalar (callEntryStateHOLFinite source callee) target heap words inputs domain heapCell frontier aligned installed returned run
  let ready:=Input.CallNormal.continuationEntry source target name returned
  have callerPhysical : Physical kind source ready heap words:=physical.of_erase kind (callEntryStateHOLFinite source callee) target source ready heap words rfl rfl
  have codeEq:= (Input.evaluation_fields (callEntryStateHOLFinite source callee) target (body kind) (some (.returned returned)) run).2.2.2
  refine ⟨funded,ready,inner,?_,?_,callerPhysical,codeEq,continued,endpoint⟩
  · simp [ready,Input.CallNormal.continuationEntry,answer,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · simp [ready,Input.CallNormal.continuationEntry,answer,setVarHOLFinite]

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.scalar_scoped_none_physical
