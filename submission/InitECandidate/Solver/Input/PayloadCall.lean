import InitECandidate.Solver.Input.PayloadProgram

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real payload call with a short slice propagates the actual SszErr50;
its caller continuation and declaration body cannot run. -/
theorem reject_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (pointer length : BitVec 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer length))
    (code : source.code.lookup (ofString "decode_payload")=some (formals,body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 2≤source.clock)
    (short : length.toNat<540) :
    evaluateHOLFiniteState source (.decCall (ofString "pl") .one (ofString "decode_payload") arguments continuation)=
      (some (.exception (ofString "SszErr") (.val (.word 50#64))),emptyLocalsHOLFinite {source with clock:=source.clock-2}) := by
  classical
  obtain ⟨callee,called,p,n⟩:=environment source.code.lookup pointer length code
  let entry:=callEntryStateHOLFinite source callee
  have rejected:=entry_execute entry length n failCode exceptionShape (by change 1≤source.clock-1; omega)
  simp only [if_pos short] at rejected
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  simp only [args,called,if_neg (show source.clock≠0 from by omega)]
  rw [rejected]
  change (some (PanSemResultExact.exception (ofString "SszErr") (.val (.word 50#64))),emptyLocalsHOLFinite {source with clock:=source.clock-1-1})=_
  rw [Nat.sub_sub]

/-- Normal execution of the caller proves the payload's fixed minimum size,
without assuming successful schema parsing or a decoded payload mirror. -/
theorem normal_length (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (pointer length : BitVec 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer length))
    (code : source.code.lookup (ofString "decode_payload")=some (formals,body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 2≤source.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString "pl") .one (ofString "decode_payload") arguments continuation)=(some (.returned value),post)) :
    540≤length.toNat := by
  by_contra small
  have rejected:=reject_call source arguments continuation pointer length args code failCode exceptionShape enough (by omega)
  have impossible:=congrArg Prod.fst (rejected.symm.trans run)
  cases impossible

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.reject_call
#print axioms InitECandidate.Solver.Input.Payload.normal_length
