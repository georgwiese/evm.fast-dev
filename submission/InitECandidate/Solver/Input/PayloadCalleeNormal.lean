import InitECandidate.Solver.Input.PayloadCall

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Invert the genuine scoped payload call: a normal caller return entails
an actual callee return. Errors, exceptions and timeout cannot supply one. -/
theorem callee_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (pointer length : BitVec 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer length))
    (code : source.code.lookup (ofString "decode_payload")=some (formals,body,.one))
    (enough : 1≤source.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString "pl") .one (ofString "decode_payload") arguments continuation)=(some (.returned value),post)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite source.code.lookup (ofString "decode_payload") (values pointer length)=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) ∧ callee.lookup (ofString "len")=some (.val (.word length)) ∧
      ∃ target returned,evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned returned),target) := by
  classical
  obtain ⟨callee,called,p,n⟩:=environment source.code.lookup pointer length code
  have actual:=evaluateHOLFiniteState_decCall_fixClockRewrite source (ofString "pl") .one (ofString "decode_payload") arguments continuation
  simp only [args,called,if_neg (show source.clock≠0 from by omega)] at actual
  have normal:=congrArg Prod.fst (actual.symm.trans run)
  generalize outputEq : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output at normal
  obtain ⟨result,target⟩:=output
  cases result with
  | none=>cases normal
  | some result=>
    cases result with
    | returned returned=>exact ⟨callee,called,p,n,target,returned,outputEq⟩
    | error=>cases normal
    | timeOut=>cases normal
    | «break»=>cases normal
    | «continue»=>cases normal
    | exception name payload=>cases normal
    | finalFfi event=>cases normal

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.callee_normal
