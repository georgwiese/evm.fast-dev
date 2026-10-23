import InitECandidate.Solver.Input.RlpLength.BytesSize
import InitECandidate.Solver.Input.LocalEffects
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input.RlpLength.BytesSize
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The unchanged byte-string size helper for every physically bounded
length with room for its at-most-nine-byte header. No input-size cap is
imposed on trie paths accumulated by original deletion/concatenation. -/
theorem general_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first n : BitVec 64) (fits : n.toNat+9<2^64)
    (fb : source.locals.lookup (ofString "first_byte")=some (.val (.word first)))
    (len : source.locals.lookup (ofString "n")=some (.val (.word n)))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 10≤source.clock) :
    ∃ target encoded paid,n.toNat≤encoded ∧ encoded≤n.toNat+9 ∧ paid≤10 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  classical
  have test:=condition_read source first n fb len
  simp only [eval] at test
  by_cases short : n=1#64 ∧ first.toNat<128
  · have nNat : n.toNat=1 := by rw [short.1]; rfl
    have guardRun : evaluateHOLFiniteState source (shortGuard condition)=(some (.returned (.val (.word 1#64))),emptyLocalsHOLFinite source) := by
      rw [shortGuard,evaluateHOLFiniteState_ite,test]
      simp only [if_pos short]
      simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    refine ⟨emptyLocalsHOLFinite source,1,0,by omega,by omega,by decide,rfl,?_,by simp [emptyLocalsHOLFinite]⟩
    rw [body_shape]
    exact WitnessRadix.StateSteps.stopped_sequence source _ _ _ (.returned (.val (.word 1#64))) guardRun (Nat.le_refl _)
  · have guardRun : evaluateHOLFiniteState source (shortGuard condition)=(none,source) := by
      rw [shortGuard,evaluateHOLFiniteState_ite,test]
      simp [short]
    have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "n"]=some [.val (.word n)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,len]
    obtain ⟨h,paid,hLow,hHigh,bound,called⟩:=Header.call_execute source n "h" [localVar "n"] returnSize args headerCode beCode enough
    let next:=bind {source with clock:=source.clock-1-paid} "h" (BitVec.ofNat 64 h)
    have hLocal : next.locals.lookup (ofString "h")=some (.val (.word (BitVec.ofNat 64 h))):=bind_lookup_same _ _ _
    have nLocal : next.locals.lookup (ofString "n")=some (.val (.word n)) :=
      (bind_lookup_other _ "h" "n" _ (by decide)).trans len
    have nWord : n=BitVec.ofNat 64 n.toNat:=by simp
    have returnRun : evaluateHOLFiniteState next returnSize=
        (some (.returned (.val (.word (BitVec.ofNat 64 (h+n.toNat))))),emptyLocalsHOLFinite next) := by
      simp [returnSize,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,hLocal,nLocal,valueIsWord,valueWord,
        wordOpHOL,wordOp,BitVec.ofNat_add,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    refine ⟨restore source "h" (emptyLocalsHOLFinite next),h+n.toNat,paid+1,by omega,by omega,by omega,?_,?_,?_⟩
    · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    · rw [body_shape,WitnessRadix.StateSteps.next_sequence source source _ _ guardRun (Nat.le_refl _)]
      change evaluateHOLFiniteState source (.decCall (ofString "h") .one (ofString "rlp_header_len") [localVar "n"] returnSize)=_
      rw [called,returnRun]
    · have subtract : source.clock-1-paid=source.clock-(paid+1) := by omega
      change emptyLocalsHOLFinite {source with clock:=source.clock-1-paid}=emptyLocalsHOLFinite {source with clock:=source.clock-(paid+1)}
      rw [subtract]

/-- Every outcome, including clock exhaustion, uses at most ten source
calls/loop ticks under the actual current scalar arguments. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first n : BitVec 64) (fits : n.toNat+9<2^64)
    (fb : source.locals.lookup (ofString "first_byte")=some (.val (.word first)))
    (len : source.locals.lookup (ofString "n")=some (.val (.word n)))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤10 := by
  by_cases enough : 10≤source.clock
  · obtain ⟨target,encoded,paid,_lower,_upper,bound,_number,run,frame⟩:=general_execute source first n fits fb len headerCode beCode enough
    have clock:=congrArg PanSemStateFiniteExact.clock frame
    change target.clock=source.clock-paid at clock
    rw [run]
    change source.clock-target.clock≤10
    omega
  · omega

/-- A genuine normal return derives the actual nonwrapping byte-string
size and unchanged nonlocal fields even with less than the conservative
clock allowance. The normal callee result is proved, not supplied. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (first n : BitVec 64) (fits : n.toNat+9<2^64)
    (fb : source.locals.lookup (ofString "first_byte")=some (.val (.word first)))
    (len : source.locals.lookup (ofString "n")=some (.val (.word n)))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ encoded,n.toNat≤encoded ∧ encoded≤n.toNat+9 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      value=.val (.word (BitVec.ofNat 64 encoded)) ∧ source.clock-target.clock≤10 ∧ LocalEffects.erase target=LocalEffects.erase source := by
  let padded:={source with clock:=source.clock+10}
  obtain ⟨post,encoded,paid,lower,upper,bound,number,run,frame⟩:=general_execute padded first n fits fb len headerCode beCode (by change 10≤source.clock+10; omega)
  have lifted:=panPropsEvaluateAddClockEq body source (some (.returned value)) target 10 ⟨normal,by intro impossible; cases impossible⟩
  have same:=lifted.symm.trans run
  have answer:=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst same))
  have postEq:=congrArg Prod.snd same
  change {target with clock:=target.clock+10}=post at postEq
  rw [←postEq] at frame
  have kept:=congrArg LocalEffects.erase frame
  have priced:=body_cost source first n fits fb len headerCode beCode
  rw [normal] at priced
  exact ⟨encoded,lower,upper,number,answer,priced,kept⟩

end InitECandidate.Solver.Input.RlpLength.BytesSize

#print axioms InitECandidate.Solver.Input.RlpLength.BytesSize.general_execute
#print axioms InitECandidate.Solver.Input.RlpLength.BytesSize.body_cost
#print axioms InitECandidate.Solver.Input.RlpLength.BytesSize.body_normal
