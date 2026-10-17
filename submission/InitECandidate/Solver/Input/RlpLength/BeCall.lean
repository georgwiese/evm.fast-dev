import InitECandidate.Solver.Input.RlpLength.BeBuilt

namespace InitECandidate.Solver.Input.RlpLength.Be
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (values value))
    (code : source.code.lookup (ofString "rlp_be_len")=some (formals,body,.one)) (enough : 9≤source.clock) :
    ∃ count,count≤8 ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_be_len") expressions continuation)=
        let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1-count} name (BitVec.ofNat 64 count)) continuation
        (output.1,restore source name output.2) := by
  obtain ⟨callee,called,p⟩:=environment source.code.lookup value code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,count,bound,bodyRun,frame⟩:=execute entry value p (by change 8≤source.clock-1; omega)
  exact ⟨count,bound,CallNormal.pure_return_execute source target name (ofString "rlp_be_len") expressions (values value) body continuation callee
    (BitVec.ofNat 64 count) count args called (by omega) bodyRun frame⟩

end InitECandidate.Solver.Input.RlpLength.Be

#print axioms InitECandidate.Solver.Input.RlpLength.Be.call_execute
