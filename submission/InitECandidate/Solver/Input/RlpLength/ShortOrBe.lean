import InitECandidate.Solver.Input.RlpLength.BeCall

namespace InitECandidate.Solver.Input.RlpLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def shortGuard (condition : ExpHOL 64) : ProgHOL 64 := .ite condition (.return (.const 1#64)) .skip
def returnOnePlus : ProgHOL 64 := .return (.op .add [.const 1#64,localVar "ll"])
def longTail (parameter : String) : ProgHOL 64 := .decCall (ofString "ll") .one (ofString "rlp_be_len") [localVar parameter] returnOnePlus

/-- Shared exact execution of the two fixed RLP size helpers: their actual
short return or real be_len call and scalar add, including lexical return. -/
theorem short_or_be_exact (source : PanSemStateFiniteExact 64 Guest.HostMemory) (parameter : String) (value : BitVec 64)
    (present : source.locals.lookup (ofString parameter)=some (.val (.word value)))
    (condition : ExpHOL 64) (short : Prop) [Decidable short]
    (test : eval source condition=some (.val (.word (if short then 1#64 else 0#64))))
    (code : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 9≤source.clock) :
    ∃ target encoded paid,encoded=(if short then 1 else Be.byteCount 8 value+1) ∧ 1≤encoded ∧ encoded≤9 ∧ paid≤9 ∧
      evaluateHOLFiniteState source (.seq (shortGuard condition) (longTail parameter))=
        (some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  classical
  simp only [eval] at test
  by_cases small : short
  · have guardRun : evaluateHOLFiniteState source (shortGuard condition)=(some (.returned (.val (.word 1#64))),emptyLocalsHOLFinite source) := by
      rw [shortGuard,evaluateHOLFiniteState_ite,test]
      simp only [if_pos small]
      simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    refine ⟨emptyLocalsHOLFinite source,1,0,by simp only [if_pos small],by decide,by decide,by decide,?_,by simp [emptyLocalsHOLFinite]⟩
    exact WitnessRadix.StateSteps.stopped_sequence source _ _ _ (.returned (.val (.word 1#64))) guardRun (Nat.le_refl _)
  · have guardRun : evaluateHOLFiniteState source (shortGuard condition)=(none,source) := by
      rw [shortGuard,evaluateHOLFiniteState_ite,test]
      simp [small]
    have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar parameter]=some (Be.values value) := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,present,Be.values]
    obtain ⟨count,exactCount,bound,callRun⟩:=Be.call_execute_exact source value "ll" [localVar parameter] returnOnePlus args code enough
    let next:=bind {source with clock:=source.clock-1-count} "ll" (BitVec.ofNat 64 count)
    have ll : next.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count))):=bind_lookup_same _ _ _
    have returnRun : evaluateHOLFiniteState next returnOnePlus=(some (.returned (.val (.word (BitVec.ofNat 64 (count+1))))),emptyLocalsHOLFinite next) := by
      simp [returnOnePlus,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,ll,valueIsWord,valueWord,wordOpHOL,wordOp,
        ←BitVec.ofNat_add,Nat.add_comm,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    refine ⟨restore source "ll" (emptyLocalsHOLFinite next),count+1,count+1,by simp only [if_neg small,exactCount],by omega,by omega,by omega,?_,?_⟩
    · rw [WitnessRadix.StateSteps.next_sequence source source _ _ guardRun (Nat.le_refl _)]
      change evaluateHOLFiniteState source (.decCall (ofString "ll") .one (ofString "rlp_be_len") [localVar parameter] returnOnePlus)=_
      rw [callRun,returnRun]
    · have subtraction : source.clock-1-count=source.clock-(count+1) := by omega
      change emptyLocalsHOLFinite {source with clock:=source.clock-1-count}=emptyLocalsHOLFinite {source with clock:=source.clock-(count+1)}
      rw [subtraction]

theorem short_or_be (source : PanSemStateFiniteExact 64 Guest.HostMemory) (parameter : String) (value : BitVec 64)
    (present : source.locals.lookup (ofString parameter)=some (.val (.word value)))
    (condition : ExpHOL 64) (short : Prop) [Decidable short]
    (test : eval source condition=some (.val (.word (if short then 1#64 else 0#64))))
    (code : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 9≤source.clock) :
    ∃ target encoded paid,1≤encoded ∧ encoded≤9 ∧ paid≤9 ∧
      evaluateHOLFiniteState source (.seq (shortGuard condition) (longTail parameter))=
        (some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  obtain ⟨target,encoded,paid,_exactCount,lower,upper,bounded,run,frame⟩:=short_or_be_exact source parameter value present condition short test code enough
  exact ⟨target,encoded,paid,lower,upper,bounded,run,frame⟩

end InitECandidate.Solver.Input.RlpLength

#print axioms InitECandidate.Solver.Input.RlpLength.short_or_be

#print axioms InitECandidate.Solver.Input.RlpLength.short_or_be_exact
