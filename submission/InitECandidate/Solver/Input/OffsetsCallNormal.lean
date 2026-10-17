import InitECandidate.Solver.Input.OffsetsCall

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal resumption after the actual decoder guard proves the first-offset
fact and changes exactly the caller's clock, including its real callee cost. -/
theorem call_normal_first {F : Type} (source post : PanSemStateFiniteExact 64 F) (expressions : List (ExpHOL 64))
    (pointer fixed total : BitVec 64) (offsets : Nat→BitVec 64) (count : Nat) (positive : 0<count) (small : count≤8)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=
      some (arguments pointer fixed total count))
    (code : source.code.lookup (ofString "ssz_check_offsets")=some (formals,body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (mapped : ∀ position<count,source.memaddrs (pointer+BitVec.ofNat 64 (8*position)))
    (cells : ∀ position<count,source.memory (pointer+BitVec.ofNat 64 (8*position))=.word (offsets position))
    (enough : count+2≤source.clock)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "ssz_check_offsets") expressions)=(none,post)) :
    offsets 0=fixed ∧ ∃ paid,paid≤count+2 ∧ post={source with clock:=source.clock-paid} := by
  obtain ⟨result,target,paid,execution,bound,frame,outcome⟩:=call_execute source expressions pointer fixed total offsets count positive small
    args code failCode exceptionShape mapped cells enough
  have equal:=run.symm.trans execution
  have resultEqual : none=result:=congrArg Prod.fst equal
  have postEqual : post=target:=congrArg Prod.snd equal
  rcases outcome with normal|fault
  · refine ⟨normal.2.1,paid,bound,?_⟩
    rw [postEqual]
    have full:=congrArg (fun state : PanSemStateFiniteExact 64 F=>{state with locals:=target.locals}) frame
    have targetEq : target={{source with clock:=source.clock-paid} with locals:=target.locals} := by
      simpa only [emptyLocalsHOLFinite] using full
    rw [normal.2.2] at targetEq
    exact targetEq
  · obtain ⟨error,allowed,exception⟩:=fault
    rw [exception] at resultEqual
    cases resultEqual

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.call_normal_first
