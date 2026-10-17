import InitECandidate.Solver.GasBudget.CallGasProgram

namespace InitECandidate.Solver.GasBudget.CallGas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual 63/64 cap, mutable g clamp and two-word return. No mathematical
bound on the requested gas is assumed; only the cap can constrain the result. -/
theorem cap_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (requested left reward : BitVec 64)
    (available : source.locals.lookup (ofString "avail")=some (.val (.word left)))
    (gas : source.locals.lookup (ofString "gas")=some (.val (.word requested)))
    (extra : source.locals.lookup (ofString "extra_gas")=some (.val (.word 0#64)))
    (stipendLocal : source.locals.lookup (ofString "stipend")=some (.val (.word reward))) :
    ∃ target,evaluateHOLFiniteState source afterAvail=(some (.returned (pair (capped requested left) (capped requested left+reward))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite source := by
  classical
  have capRead : eval source capExpression=some (.val (.word (cap left))) := by
    simp [eval,capExpression,evalHOLExact,evalListHOLExact,toExact,localVar,available,wordShiftHOL,valueIsWord,valueWord,wordOpHOL,wordOp,cap]
  let sm:=bind source "mx" (cap left)
  let sg:=bind sm "g" requested
  have gasM : sm.locals.lookup (ofString "gas")=some (.val (.word requested)):=
    (bind_lookup_other _ "mx" "gas" _ (by decide)).trans gas
  have requestedRead : eval sm (localVar "gas")=some (.val (.word requested)) := by simp [eval,localVar,evalHOLExact,toExact,gasM]
  have mxG : sg.locals.lookup (ofString "mx")=some (.val (.word (cap left))):=
    (bind_lookup_other _ "g" "mx" _ (by decide)).trans (bind_lookup_same _ _ _)
  have gG : sg.locals.lookup (ofString "g")=some (.val (.word requested)):=bind_lookup_same _ _ _
  have mxRead : eval sg (localVar "mx")=some (.val (.word (cap left))) := by simp [eval,localVar,evalHOLExact,toExact,mxG]
  have assigned:=WitnessRadix.StateSteps.assign_execute sg "g" (localVar "mx") requested (cap left) gG mxRead
  let sc:=if cap left<requested then bind sg "g" (cap left) else sg
  have clampRun : evaluateHOLFiniteState sg clamp=(none,sc) := by
    rw [clamp,evaluateHOLFiniteState_ite]
    by_cases less : cap left<requested
    · simpa [evalHOLExact,toExact,localVar,mxG,gG,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,less,sc] using assigned
    · simp [evalHOLExact,toExact,localVar,mxG,gG,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,less,sc]
  have gC : sc.locals.lookup (ofString "g")=some (.val (.word (capped requested left))) := by
    by_cases less : cap left<requested
    · simpa only [sc,capped,if_pos less] using (bind_lookup_same sg "g" (cap left))
    · simpa only [sc,capped,if_neg less] using gG
  have others : ∀ name : String,ofString "g"≠ofString name→ sc.locals.lookup (ofString name)=sm.locals.lookup (ofString name) := by
    intro name different
    by_cases less : cap left<requested
    · change (if cap left<requested then bind sg "g" (cap left) else sg).locals.lookup (ofString name)=_
      rw [if_pos less]
      exact (bind_lookup_other _ "g" name _ different).trans (bind_lookup_other _ "g" name _ different)
    · change (if cap left<requested then bind sg "g" (cap left) else sg).locals.lookup (ofString name)=_
      rw [if_neg less]
      exact bind_lookup_other _ "g" name _ different
  have extraC : sc.locals.lookup (ofString "extra_gas")=some (.val (.word 0#64)):=
    (others "extra_gas" (by decide)).trans ((bind_lookup_other _ "mx" "extra_gas" _ (by decide)).trans extra)
  have stipendC : sc.locals.lookup (ofString "stipend")=some (.val (.word reward)):=
    (others "stipend" (by decide)).trans ((bind_lookup_other _ "mx" "stipend" _ (by decide)).trans stipendLocal)
  have returnRun : evaluateHOLFiniteState sc returnAmounts=
      (some (.returned (pair (capped requested left) (capped requested left+reward))),emptyLocalsHOLFinite sc) := by
    simp [returnAmounts,pair,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,gC,extraC,stipendC,
      valueIsWord,valueWord,wordOpHOL,wordOp,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have clock : sc.clock=sg.clock := by dsimp [sc]; split <;> rfl
  have gRun : evaluateHOLFiniteState sg afterG=
      (some (.returned (pair (capped requested left) (capped requested left+reward))),emptyLocalsHOLFinite sc) := by
    rw [afterG,WitnessRadix.StateSteps.next_sequence sg sc _ _ clampRun (by omega)]
    exact returnRun
  have gScope:=Input.ScalarScope.declare_execute sm _ "g" (localVar "gas") requested afterG _ requestedRead gRun
  let target:=restore source "mx" (restore sm "g" (emptyLocalsHOLFinite sc))
  refine ⟨target,?_,?_⟩
  · rw [afterAvail]
    exact Input.ScalarScope.declare_execute source _ "mx" capExpression (cap left) _ _ capRead gScope
  · dsimp [target,sc]
    split <;> rfl

end InitECandidate.Solver.GasBudget.CallGas

#print axioms InitECandidate.Solver.GasBudget.CallGas.cap_execute
