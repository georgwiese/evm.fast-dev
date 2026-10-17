import InitECandidate.Solver.Input.RlpWrite.PutBeBuilt

namespace InitECandidate.Solver.Input.RlpWrite.PutBe
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst value : BitVec 64) (count : Nat)
    (expressions : List (ExpHOL 64)) (small : count<2^64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=
      some [.val (.word dst),.val (.word value),.val (.word (BitVec.ofNat 64 count))])
    (code : source.code.lookup (ofString "rlp_put_be")=some (formals,body,.one))
    (mapped : ∀ index<count,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))) (enough : count+1≤source.clock) :
    ∃ memory,evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_put_be") expressions)=
      (none,{source with memory:=memory,clock:=source.clock-1-count}) ∧
      (∀ query,(∀ index<count,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))→memory query=source.memory query) := by
  classical
  obtain ⟨callee,called,d,v,n⟩:=environment source.code.lookup dst value (BitVec.ofNat 64 count) code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,bodyRun,frame,memory⟩:=execute entry dst value count small d n v mapped (by change count≤source.clock-1; omega)
  have actual:=evaluateHOLFiniteState_call_return_caller_locals source none (ofString "rlp_put_be") expressions
    [.val (.word dst),.val (.word value),.val (.word (BitVec.ofNat 64 count))] body callee .one (.val (.word 0#64)) target args called (by omega) bodyRun
      (by simp [shapeOfHOLExact,shapeEqHOL])
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  refine ⟨target.memory,?_,memory⟩
  exact actual.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>(none,state)) callerFrame)

end InitECandidate.Solver.Input.RlpWrite.PutBe

#print axioms InitECandidate.Solver.Input.RlpWrite.PutBe.call_execute
