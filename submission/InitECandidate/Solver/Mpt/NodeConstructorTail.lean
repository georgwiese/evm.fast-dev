import InitECandidate.Solver.Mpt.NodeConstructorPhysicalFrame
import InitECandidate.Solver.Input.TailCallNormal
import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual original scalar tail call returns its genuine allocation
and retains the physical constructor contract after clearing caller locals. -/
theorem scalar_tail_physical (kind : Kind) (scalar : kind≠.branch)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (words : String → BitVec 64)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64)) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some values)
    (expectedCall : lookupCodeHOLFinite source.code.lookup (ofString (NodeConstructor.name kind)) values=some (body kind,callee,.one))
    (inputs : Inputs kind (callEntryStateHOLFinite source callee) words)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.call none (ofString (NodeConstructor.name kind)) arguments)=(some (.returned value),post)) :
    value=.val (.word heap) ∧ Physical kind source post heap words ∧ post.code=source.code ∧ source.clock-post.clock≤3 := by
  obtain ⟨funded,target,run,checked,endpoint⟩:=Input.CallNormal.tail_callee_return source post (ofString (NodeConstructor.name kind)) arguments values (body kind) callee .one argsRead expectedCall value normal
  obtain ⟨answer,physical⟩:=scalar_physical kind scalar (callEntryStateHOLFinite source callee) target heap words inputs domain heapCell frontier aligned installed value run
  have callerPhysical:=physical.of_erase kind (callEntryStateHOLFinite source callee) target source post heap words rfl (by rw [endpoint]; rfl)
  have codeEq:=(Input.evaluation_fields source post (.call none (ofString (NodeConstructor.name kind)) arguments) (some (.returned value)) normal).2.2.2
  have price:=Input.ClockCost.call_body source.code none (ofString (NodeConstructor.name kind)) arguments (formals kind) (body kind) .one 2
    (original_code kind source.code installed) (scalar_body_price kind scalar source.code installed)
  have spent:=price source rfl
  change source.clock-(evaluateHOLFiniteState source (.call none (ofString (NodeConstructor.name kind)) arguments)).2.clock≤3 at spent
  rw [normal] at spent
  exact ⟨answer,callerPhysical,codeEq,spent⟩

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.scalar_tail_physical
