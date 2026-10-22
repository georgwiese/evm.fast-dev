import InitECandidate.Solver.Input.RunAttemptPayloadHeaderProgram
import InitECandidate.Solver.Input.ScopedCallObserve
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Input.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def PayloadHeaderResumes (caller target post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (childResult outcome : Option (PanSemResultExact 64)) : Prop :=
  post.clock=target.clock ∨ ∃ returned inner,
    childResult=some (.returned returned) ∧
    (shapeEqHOL (shapeOfHOLExact returned) .one && shapeEqHOL (shapeOfHOLExact returned) .one)=true ∧
    evaluateHOLFiniteState (CallNormal.continuationEntry caller target "hdr" returned) afterPayloadHeader=(outcome,inner) ∧
    post=QueryBranch.restore caller "hdr" inner

/-- Actual original815 enters payload_header with its real saved SI and
caller. The child outcome is observed before assigning it a full bound. -/
theorem payload_header_call_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (si : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (siCell : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterTransactionScan=(outcome,post)) :
    source.clock-post.clock≤1 ∨ ∃ entry target childResult,
      LocalEffects.erase entry=LocalEffects.erase source ∧ entry.clock=source.clock-1 ∧
      entry.locals.lookup (ofString "si")=some (.val (.word si)) ∧
      evaluateHOLFiniteState entry PayloadHeader.body=(childResult,target) ∧ PayloadHeaderResumes source target post childResult outcome := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) payloadHeaderArguments=some (PayloadHeader.values si):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,payloadHeaderArguments,QueryBranch.localVar,siCell,PayloadHeader.values]
  obtain ⟨callee,called,entrySI⟩:=PayloadHeader.environment source.code.lookup si (PayloadHeader.original_code source.code installed)
  rw [payload_header_shapes.1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip,payload_header_shapes.2] at run
  rcases CallNormal.scoped_observe source post "hdr" .one (ofString "payload_header") payloadHeaderArguments (PayloadHeader.values si)
    PayloadHeader.body afterPayloadHeader callee .one args called outcome run with stopped|observed
  · exact Or.inl stopped
  · obtain ⟨childResult,target,funded,childRun,remaining⟩:=observed
    exact Or.inr ⟨callEntryStateHOLFinite source callee,target,childResult,rfl,rfl,entrySI,childRun,remaining⟩

end InitECandidate.Solver.Input.RunAttempt

#print axioms InitECandidate.Solver.Input.RunAttempt.payload_header_call_trace
