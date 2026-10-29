import InitECandidate.Solver.Input.RlpLength.BytesSize
import InitECandidate.Solver.Input.PureAssignReturn

namespace InitECandidate.Solver.Input.RlpLength.BytesSize
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem assign_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first n old : BitVec 64) (name : String)
    (expressions : List (ExpHOL 64)) (small : n.toNat≤251655056)
    (present : source.locals.lookup (ofString name)=some (.val (.word old)))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word first),.val (.word n)])
    (code : source.code.lookup (ofString "rlp_bytes_encoded_len")=some (formals,body,.one))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 11≤source.clock) :
    ∃ encoded paid,n.toNat≤encoded ∧ encoded≤n.toNat+9 ∧ paid≤10 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString "rlp_bytes_encoded_len") expressions)=
        (none,bind {source with clock:=source.clock-1-paid} name (BitVec.ofNat 64 encoded)) := by
  obtain ⟨callee,called,fb,len⟩:=environment source.code.lookup first n code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,encoded,paid,lower,upper,bound,number,bodyRun,frame⟩:=execute entry first n small fb len headerCode beCode (by change 10≤source.clock-1; omega)
  exact ⟨encoded,paid,lower,upper,bound,number,CallNormal.pure_assign_execute source target name old (ofString "rlp_bytes_encoded_len") expressions
    [.val (.word first),.val (.word n)] body callee (BitVec.ofNat 64 encoded) paid present args called (by omega) bodyRun frame⟩

end InitECandidate.Solver.Input.RlpLength.BytesSize

#print axioms InitECandidate.Solver.Input.RlpLength.BytesSize.assign_execute
