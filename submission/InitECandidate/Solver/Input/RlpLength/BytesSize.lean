import InitECandidate.Solver.Input.RlpLength.BytesSizeProgram

namespace InitECandidate.Solver.Input.RlpLength.BytesSize
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Exact actual byte-string size function for input-sized records. Both
branches return a natural size in[n,n+9], without word-addition overflow. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first n : BitVec 64) (small : n.toNat≤251655056)
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

end InitECandidate.Solver.Input.RlpLength.BytesSize

#print axioms InitECandidate.Solver.Input.RlpLength.BytesSize.execute
