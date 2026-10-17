import InitECandidate.Solver.Input.RlpLength.ScalarSizes

namespace InitECandidate.Solver.Input.RlpLength.ListHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_rlp_list_header_len with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "payload_len",.one)]
def arguments : List (ExpHOL 64) := [localVar "payload_len"]

theorem body_shape : body=.call none (ofString "rlp_header_len") arguments := by
  simp only [body,Guest.guestFn_rlp_list_header_len,progToHOL,expToHOL,List.map_cons,List.map_nil,Option.map_none,arguments,localVar]

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (n : source.locals.lookup (ofString "payload_len")=some (.val (.word value)))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 10≤source.clock) :
    ∃ target encoded paid,1≤encoded ∧ encoded≤9 ∧ paid≤10 ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  classical
  obtain ⟨callee,called,p⟩:=CallNormal.unary_environment source.code.lookup (ofString "rlp_header_len") "n" Header.body value headerCode
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,encoded,paid,lower,upper,bound,bodyRun,frame⟩:=Header.execute entry value p beCode (by change 9≤source.clock-1; omega)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word value)] := by
    simp [arguments,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,n]
  have actual:=evaluateHOLFiniteState_call_return_none source (.val (.word (BitVec.ofNat 64 encoded))) (ofString "rlp_header_len") arguments
    [.val (.word value)] Header.body callee .one target args called (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨emptyLocalsHOLFinite target,encoded,paid+1,lower,upper,by omega,?_,?_⟩
  · rw [body_shape]
    exact actual
  · change emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-(paid+1)}
    change emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1-paid} at frame
    have subtraction : source.clock-1-paid=source.clock-(paid+1) := by omega
    simpa only [subtraction] using frame

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word value)])
    (code : source.code.lookup (ofString "rlp_list_header_len")=some (formals,body,.one))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 11≤source.clock) :
    ∃ encoded paid,1≤encoded ∧ encoded≤9 ∧ paid≤10 ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_list_header_len") expressions continuation)=
        let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1-paid} name (BitVec.ofNat 64 encoded)) continuation
        (output.1,restore source name output.2) := by
  obtain ⟨callee,called,n⟩:=CallNormal.unary_environment source.code.lookup (ofString "rlp_list_header_len") "payload_len" body value code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,encoded,paid,lower,upper,bound,bodyRun,frame⟩:=execute entry value n headerCode beCode (by change 10≤source.clock-1; omega)
  exact ⟨encoded,paid,lower,upper,bound,CallNormal.pure_return_execute source target name (ofString "rlp_list_header_len") expressions [.val (.word value)]
    body continuation callee (BitVec.ofNat 64 encoded) paid args called (by omega) bodyRun frame⟩

end InitECandidate.Solver.Input.RlpLength.ListHeader

#print axioms InitECandidate.Solver.Input.RlpLength.ListHeader.execute
#print axioms InitECandidate.Solver.Input.RlpLength.ListHeader.call_execute
