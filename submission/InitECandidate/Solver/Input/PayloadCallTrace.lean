import InitECandidate.Solver.Input.PayloadProgram
import InitECandidate.Solver.Input.SszGuardTrace
import InitECandidate.Solver.Input.NonTimeoutScopedCall
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "decode_payload") = some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 189 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_decode_payload) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Scalar.payloadBody,Guest.guestFn_decode_payload,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- Real payload caller and minimum-length guard on every actual enclosing
non-timeout execution. Short slices raise the original SszErr50 within two
caller/body ticks; passing reaches the actual remaining callee body. -/
theorem call_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (pointer length : BitVec 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values pointer length))
    (code : source.code.lookup (ofString "decode_payload") = some (formals,body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail") = some (SszFail.formals,SszFail.body,.one))
    (shape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString "pl") .one (ofString "decode_payload") arguments continuation) = (result,post))
    (notTimeout : result ≠ some .timeOut) :
    (length.toNat < 540 ∧ result = some (.exception (ofString "SszErr") (.val (.word 50#64))) ∧ source.clock - post.clock ≤ 2) ∨
    (540 ≤ length.toNat ∧ ∃ (callee : HolFiniteMapExact MlS (ValueHOL 64)) (bodyResult : Option (PanSemResultExact 64)) (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory),
      lookupCodeHOLFinite source.code.lookup (ofString "decode_payload") (values pointer length) = some (body,callee,.one) ∧
      callee.lookup (ofString "p") = some (.val (.word pointer)) ∧ callee.lookup (ofString "len") = some (.val (.word length)) ∧
      1 ≤ source.clock ∧ bodyResult ≠ some .timeOut ∧ evaluateHOLFiniteState (callEntryStateHOLFinite source callee) afterGuard = (bodyResult,bodyPost)) := by
  obtain ⟨callee,called,p,n⟩ := environment source.code.lookup pointer length code
  obtain ⟨funded,bodyNotTimeout⟩ := scoped_call_non_timeout source post (ofString "pl") .one (ofString "decode_payload") arguments (values pointer length)
    body continuation callee .one args called result run notTimeout
  let entry := callEntryStateHOLFinite source callee
  change (evaluateHOLFiniteState entry body).1 ≠ some .timeOut at bodyNotTimeout
  generalize computed : evaluateHOLFiniteState entry body = output at bodyNotTimeout
  obtain ⟨bodyResult,bodyPost⟩ := output
  have guardRun : evaluateHOLFiniteState entry (.seq lengthGuard afterGuard) = (bodyResult,bodyPost) := by rw [← body_shape]; exact computed
  have test := length_test_read entry length n
  rcases Header.guard_trace entry bodyPost lengthTest 50#64 (length.toNat < 540) afterGuard test failCode shape bodyResult guardRun bodyNotTimeout with short | valid
  · obtain ⟨tooShort,_,same,endpoint⟩ := short
    have actualBody : evaluateHOLFiniteState entry body = (some (.exception (ofString "SszErr") (.val (.word 50#64))),bodyPost) := by rw [computed,same]
    have actual := run
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at actual
    simp only [args,called,if_neg (show source.clock ≠ 0 by omega)] at actual
    rw [actualBody] at actual
    have resultEq := congrArg Prod.fst actual
    have endpointClock := congrArg (fun output => output.2.clock) actual
    change some (PanSemResultExact.exception (ofString "SszErr") (.val (.word 50#64))) = result at resultEq
    change bodyPost.clock = post.clock at endpointClock
    have bodyClock : bodyPost.clock = source.clock - 1 - 1 := by rw [endpoint]; rfl
    exact Or.inl ⟨tooShort,resultEq.symm,by rw [← endpointClock,bodyClock]; omega⟩
  · exact Or.inr ⟨by omega,callee,bodyResult,bodyPost,called,p,n,funded,bodyNotTimeout,valid.2⟩

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.original_code
#print axioms InitECandidate.Solver.Input.Payload.call_trace
