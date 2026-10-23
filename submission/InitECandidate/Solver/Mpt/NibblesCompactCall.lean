import InitECandidate.Solver.Mpt.NibblesCompactNormal
import InitECandidate.Solver.Input.AssignedCallKnown
import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Mpt.NibblesCompact
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open KeyToNibbles (SpanFrame)

/-- The original begin routine's real assigned compact-writer call
derives its exact length, restored caller locals and bounded write span. -/
theorem assigned_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length leaf destination : BitVec 64) (installed : Input.OriginalCode.Installed source.code)
    (name : MlS) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word pointer),.val (.word length),.val (.word leaf),.val (.word destination)])
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "nibble_list_to_compact") arguments)=(none,target)) :
    ∃ output : BitVec 64,target.locals.lookup name=some (.val (.word output)) ∧ output.toNat=length.toNat/2+1 ∧
      (∀ other,name≠other→target.locals.lookup other=source.locals.lookup other) ∧
      source.clock-target.clock≤length.toNat/2+1 ∧ SpanFrame source target destination (length.toNat/2+1) := by
  obtain ⟨callee,called,_pointerCell,lengthCell,leafCell,destinationCell⟩:=environment source pointer length leaf destination (original_code source.code installed)
  obtain ⟨_funded,childTarget,returned,run,endpoint⟩:=Input.CallNormal.local_known source target name (ofString "nibble_list_to_compact") arguments _ body callee .one args called normal
  obtain ⟨output,answer,size,price,frame⟩:=body_normal (callEntryStateHOLFinite source callee) childTarget length leaf destination lengthCell leafCell destinationCell returned run
  refine ⟨output,?_,size,?_,?_,?_⟩
  · rw [endpoint,answer]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · intro other different
    rw [endpoint]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]
  · rw [endpoint]
    change source.clock-childTarget.clock≤length.toNat/2+1
    change source.clock-1-childTarget.clock≤length.toNat/2 at price
    omega
  · rw [endpoint]
    exact ⟨frame.fields,frame.memory⟩

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length leaf destination : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (result : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word pointer),.val (.word length),.val (.word leaf),.val (.word destination)]) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo result) (ofString "nibble_list_to_compact") arguments)).2.clock≤length.toNat/2+1 := by
  obtain ⟨callee,called,_pointerCell,lengthCell,leafCell,_destinationCell⟩:=environment source pointer length leaf destination (original_code source.code installed)
  exact Input.ClockCost.call_current source result (ofString "nibble_list_to_compact") arguments _ body callee .one (length.toNat/2) args called
    (body_cost (callEntryStateHOLFinite source callee) length leaf lengthCell leafCell)

end InitECandidate.Solver.Mpt.NibblesCompact

#print axioms InitECandidate.Solver.Mpt.NibblesCompact.assigned_normal
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.call_cost
