import InitECandidate.Solver.Input.RlpLength.ListHeader
import InitECandidate.Solver.Input.PureAssignReturn

namespace InitECandidate.Solver.Input.RlpLength.ListHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem assign_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value old : BitVec 64) (name : String)
    (expressions : List (ExpHOL 64)) (present : source.locals.lookup (ofString name)=some (.val (.word old)))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word value)])
    (code : source.code.lookup (ofString "rlp_list_header_len")=some (formals,body,.one))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 11≤source.clock) :
    ∃ encoded paid,1≤encoded ∧ encoded≤9 ∧ paid≤10 ∧
      evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString "rlp_list_header_len") expressions)=
        (none,bind {source with clock:=source.clock-1-paid} name (BitVec.ofNat 64 encoded)) := by
  obtain ⟨callee,called,n⟩:=CallNormal.unary_environment source.code.lookup (ofString "rlp_list_header_len") "payload_len" body value code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,encoded,paid,lower,upper,bound,bodyRun,frame⟩:=execute entry value n headerCode beCode (by change 10≤source.clock-1; omega)
  exact ⟨encoded,paid,lower,upper,bound,CallNormal.pure_assign_execute source target name old (ofString "rlp_list_header_len") expressions
    [.val (.word value)] body callee (BitVec.ofNat 64 encoded) paid present args called (by omega) bodyRun frame⟩

end InitECandidate.Solver.Input.RlpLength.ListHeader

#print axioms InitECandidate.Solver.Input.RlpLength.ListHeader.assign_execute
