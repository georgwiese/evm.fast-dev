import InitECandidate.Solver.Input.FixedList.Program

namespace InitECandidate.Solver.Input.FixedList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem tail_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (q r limit : BitVec 64)
    (qr : source.locals.lookup (ofString "qr")=some (UDivMod.pairValue q r))
    (lim : source.locals.lookup (ofString "lim")=some (.val (.word limit)))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source tail=(some (.returned value),post)) :
    r=0#64 ∧ q.toNat≤limit.toNat ∧ value=.val (.word q) ∧ post=emptyLocalsHOLFinite source := by
  classical
  have remTest : eval source remainderTest=some (.val (.word (if r≠0#64 then 1#64 else 0#64))) := by
    by_cases zero : r=0#64 <;>
      simp [eval,remainderTest,remainder,localVar,UDivMod.pairValue,evalHOLExact,toExact,qr,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]
  have limTest : eval source limitTest=some (.val (.word (if limit.toNat<q.toNat then 1#64 else 0#64))) := by
    simp [eval,limitTest,quotient,localVar,UDivMod.pairValue,evalHOLExact,toExact,qr,lim,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  change evaluateHOLFiniteState source (.seq _ limitTail)=_ at run
  obtain ⟨remainderZero,limitRun⟩:=guard_normal source post remainderTest 30#64 (r≠0#64) remTest failCode exceptionShape enough limitTail value run
  change evaluateHOLFiniteState source (.seq _ returnCount)=_ at limitRun
  obtain ⟨limitBound,returnNormal⟩:=guard_normal source post limitTest 31#64 (limit.toNat<q.toNat) limTest failCode exceptionShape enough returnCount value limitRun
  have returnRun : evaluateHOLFiniteState source returnCount=(some (.returned (.val (.word q))),emptyLocalsHOLFinite source) := by
    simp [returnCount,quotient,localVar,UDivMod.pairValue,evaluateHOLFiniteState_return,evalHOLExact,toExact,qr,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have results:=returnRun.symm.trans returnNormal
  have returnedEq:=congrArg Prod.fst results
  have valueEq : value=.val (.word q) := by cases returnedEq; rfl
  exact ⟨by simpa using remainderZero,by omega,valueEq,(congrArg Prod.snd results).symm⟩

end InitECandidate.Solver.Input.FixedList

#print axioms InitECandidate.Solver.Input.FixedList.tail_normal
