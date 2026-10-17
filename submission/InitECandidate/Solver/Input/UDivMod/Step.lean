import InitECandidate.Solver.Input.UDivMod.Program

namespace InitECandidate.Solver.Input.UDivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem loop_test (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) (small : index≤64)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source loopTest=some (.val (.word (if 0<index then 1#64 else 0#64))) := by
  classical
  have sign : index<9223372036854775808 := by omega
  have encoded : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [eval,loopTest,localVar,evalHOLExact,toExact,i,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,BitVec.lt_def,encoded,sign]

theorem body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b q r : BitVec 64) (index : Nat)
    (positive : 0<index) (small : index≤64)
    (aLocal : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b")=some (.val (.word b)))
    (qLocal : source.locals.lookup (ofString "q")=some (.val (.word q)))
    (rLocal : source.locals.lookup (ofString "r")=some (.val (.word r)))
    (iLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    evaluateHOLFiniteState source loopBody=(none,step source a b q r index) := by
  classical
  have subtraction:=BitVec.ofNat_sub_ofNat_of_le (w:=64) index 1 (by decide) positive
  have indexRead : eval source indexExpression=some (.val (.word (BitVec.ofNat 64 (index-1)))) := by
    simp [eval,indexExpression,localVar,evalHOLExact,evalListHOLExact,toExact,iLocal,valueIsWord,valueWord,wordOpHOL,wordOp,subtraction]
  have indexRun:=WitnessRadix.StateSteps.assign_execute source "i" indexExpression _ _ iLocal indexRead
  let first:=bind source "i" (BitVec.ofNat 64 (index-1))
  have aFirst : first.locals.lookup (ofString "a")=some (.val (.word a)) := (bind_lookup_other source "i" "a" _ (by decide)).trans aLocal
  have rFirst : first.locals.lookup (ofString "r")=some (.val (.word r)) := (bind_lookup_other source "i" "r" _ (by decide)).trans rLocal
  have iFirst : first.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index-1)))) := bind_lookup_same _ _ _
  have encoded : (BitVec.ofNat 64 (index-1)).toNat=index-1 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have shiftBound : ¬(index-1≠0 ∧ 64≤index-1) := by omega
  have remainderRead : eval first remainderExpression=some (.val (.word (shifted a r index))) := by
    simp [eval,remainderExpression,localVar,evalHOLExact,evalListHOLExact,toExact,aFirst,rFirst,iFirst,valueIsWord,valueWord,
      wordOpHOL,wordOp,wordShiftHOL,shifted,encoded,shiftBound,OrOp.or,AndOp.and]
  have remainderRun:=WitnessRadix.StateSteps.assign_execute first "r" remainderExpression _ _ rFirst remainderRead
  let second:=bind first "r" (shifted a r index)
  have rSecond : second.locals.lookup (ofString "r")=some (.val (.word (shifted a r index))) := bind_lookup_same _ _ _
  have bSecond : second.locals.lookup (ofString "b")=some (.val (.word b)) :=
    (bind_lookup_other first "r" "b" _ (by decide)).trans ((bind_lookup_other source "i" "b" _ (by decide)).trans bLocal)
  have qSecond : second.locals.lookup (ofString "q")=some (.val (.word q)) :=
    (bind_lookup_other first "r" "q" _ (by decide)).trans ((bind_lookup_other source "i" "q" _ (by decide)).trans qLocal)
  have iSecond : second.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index-1)))) :=
    (bind_lookup_other first "r" "i" _ (by decide)).trans iFirst
  have test : eval second subtractTest=some (.val (.word (if takeSubtract a b r index then 1#64 else 0#64))) := by
    by_cases take : takeSubtract a b r index <;>
      simp [eval,subtractTest,localVar,evalHOLExact,toExact,rSecond,bSecond,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.le_def,takeSubtract,take]
    all_goals rfl
  simp only [eval] at test
  rw [loopBody,WitnessRadix.StateSteps.next_sequence source first _ _ indexRun (Nat.le_refl _),
    WitnessRadix.StateSteps.next_sequence first second _ _ remainderRun (Nat.le_refl _),evaluateHOLFiniteState_ite,test]
  by_cases take : takeSubtract a b r index
  · simp only [if_pos take]
    have readR : eval second subtractExpression=some (.val (.word (shifted a r index-b))) := by
      simp [eval,subtractExpression,localVar,evalHOLExact,evalListHOLExact,toExact,rSecond,bSecond,valueIsWord,valueWord,wordOpHOL,wordOp]
    have runR:=WitnessRadix.StateSteps.assign_execute second "r" subtractExpression _ _ rSecond readR
    let third:=bind second "r" (shifted a r index-b)
    have qThird : third.locals.lookup (ofString "q")=some (.val (.word q)) := (bind_lookup_other second "r" "q" _ (by decide)).trans qSecond
    have iThird : third.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index-1)))) := (bind_lookup_other second "r" "i" _ (by decide)).trans iSecond
    have readQ : eval third quotientExpression=some (.val (.word (q ||| (1#64<<<(index-1))))) := by
      simp [eval,quotientExpression,localVar,evalHOLExact,evalListHOLExact,toExact,qThird,iThird,valueIsWord,valueWord,
        wordOpHOL,wordOp,wordShiftHOL,encoded,shiftBound,OrOp.or]
    have runQ:=WitnessRadix.StateSteps.assign_execute third "q" quotientExpression _ _ qThird readQ
    change evaluateHOLFiniteState second subtractBody=(none,step source a b q r index)
    rw [subtractBody,WitnessRadix.StateSteps.next_sequence second third _ _ runR (Nat.le_refl _)]
    simpa only [step,if_pos take] using runQ
  · simp only [if_neg take]
    change evaluateHOLFiniteState second .skip=(none,step source a b q r index)
    simp only [evaluateHOLFiniteState_skip,step,if_neg take]
    rfl

end InitECandidate.Solver.Input.UDivMod

#print axioms InitECandidate.Solver.Input.UDivMod.loop_test
#print axioms InitECandidate.Solver.Input.UDivMod.body_execute
