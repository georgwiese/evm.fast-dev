import InitECandidate.Solver.Mpt.NodeNeedsRlp
import InitECandidate.Solver.Input.AssignedCallKnown
import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Mpt.NodeNeedsRlp
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The original fill loop's actual assigned helper call derives its
literal decision and exact one-tick read-only caller state. -/
theorem assigned_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (child tag cached : BitVec 64) (installed : Input.OriginalCode.Installed source.code)
    (header : child≠0#64→source.memaddrs child ∧ source.memory child=.word tag)
    (cache : child≠0#64→tag≠0#64→source.memaddrs (child+8#64) ∧ source.memory (child+8#64)=.word cached)
    (name : MlS) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word child)])
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "_node_needs_rlp") arguments)=(none,target)) :
    target=setVarHOLFinite name (.val (.word (if child=0#64 ∨ tag=0#64 ∨ cached≠0#64 then 0#64 else 1#64))) {source with clock:=source.clock-1} := by
  obtain ⟨callee,called,childCell⟩:=environment source.code.lookup child (original_code source.code installed)
  obtain ⟨_funded,childTarget,returned,run,endpoint⟩:=Input.CallNormal.local_known source target name (ofString "_node_needs_rlp") arguments _ body callee .one args called normal
  have actual:=execute (callEntryStateHOLFinite source callee) child tag cached childCell header cache
  have valueEq:=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst (run.symm.trans actual)))
  have childEq:=congrArg Prod.snd (run.symm.trans actual)
  change childTarget=emptyLocalsHOLFinite (callEntryStateHOLFinite source callee) at childEq
  rw [endpoint,valueEq,childEq]
  rfl

theorem call_cost (code) (installed : Input.OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    Input.ClockCost.Bound code (.call (Input.LocalEffects.callInfo destination) (ofString "_node_needs_rlp") arguments) 1 :=
  Input.ClockCost.call_body code destination (ofString "_node_needs_rlp") arguments formals body .one 0 (original_code code installed) (body_cost code)

end InitECandidate.Solver.Mpt.NodeNeedsRlp

#print axioms InitECandidate.Solver.Mpt.NodeNeedsRlp.assigned_normal
#print axioms InitECandidate.Solver.Mpt.NodeNeedsRlp.call_cost
