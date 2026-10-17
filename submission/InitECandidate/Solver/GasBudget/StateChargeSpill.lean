import InitECandidate.Solver.GasBudget.StateChargeProgram

namespace InitECandidate.Solver.GasBudget.StateCharge
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def spillWrites (frame gas state spill amount : BitVec 64) : List (BitVec 64×BitVec 64) :=
  [(frame+72#64,0#64),(frame+64#64,gas-(amount-state)),(frame+192#64,spill+(amount-state))]

/-- Exact successful spill branch: declare the deficit, clear the state pool,
debit regular gas and record its outstanding state spill. -/
theorem spill_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas state spill amount : BitVec 64)
    (pools : Pools source frame gas state spill)
    (amountLocal : source.locals.lookup (ofString "amount")=some (.val (.word amount)))
    (stateLocal : source.locals.lookup (ofString "sgl")=some (.val (.word state)))
    (gasLocal : source.locals.lookup (ofString "gl")=some (.val (.word gas))) :
    ∃ target,evaluateHOLFiniteState source spillCode=(some (.returned (.val (.word 0#64))),target) ∧
      target.memory=WitnessRadix.WordWrites.write source.memory (spillWrites frame gas state spill amount) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory} := by
  classical
  let remnant:=amount-state
  have remRead : eval source remainderExpression=some (.val (.word remnant)) := by
    simp [eval,remainderExpression,evalHOLExact,evalListHOLExact,toExact,localVar,amountLocal,stateLocal,valueIsWord,valueWord,wordOpHOL,wordOp,remnant]
  let entered:=bind source "rem" remnant
  have remE : entered.locals.lookup (ofString "rem")=some (.val (.word remnant)):=bind_lookup_same _ _ _
  have gasE : entered.locals.lookup (ofString "gl")=some (.val (.word gas)):=
    (bind_lookup_other _ "rem" "gl" _ (by decide)).trans gasLocal
  have firstRun:=WitnessRadix.StoreWord.execute entered (frameAddress 72#64) (.const 0#64) (frame+72#64) 0#64
    (address_read entered frame 72#64 pools.ev) rfl (pools.mapped 72 (by simp))
  let first:={entered with memory:=WitnessRadix.StoreWord.put entered.memory (frame+72#64) 0#64}
  have remF : first.locals.lookup (ofString "rem")=some (.val (.word remnant)):=remE
  have gasF : first.locals.lookup (ofString "gl")=some (.val (.word gas)):=gasE
  have gasRead : eval first spillGasExpression=some (.val (.word (gas-remnant))) := by
    simp [eval,spillGasExpression,evalHOLExact,evalListHOLExact,toExact,localVar,remF,gasF,valueIsWord,valueWord,wordOpHOL,wordOp]
  have secondRun:=WitnessRadix.StoreWord.execute first (frameAddress 64#64) spillGasExpression (frame+64#64) (gas-remnant)
    (address_read first frame 64#64 pools.ev) gasRead (pools.mapped 64 (by simp))
  let second:={first with memory:=WitnessRadix.StoreWord.put first.memory (frame+64#64) (gas-remnant)}
  have spillSecond : second.memory (frame+192#64)=.word spill := by
    simp only [second,first,WitnessRadix.StoreWord.put,
      if_neg (offsets_ne frame 192#64 64#64 (by decide)),if_neg (offsets_ne frame 192#64 72#64 (by decide))]
    exact pools.spill
  have spillRead:=frame_read second frame 192#64 spill pools.ev (pools.mapped 192 (by simp)) spillSecond
  have remS : second.locals.lookup (ofString "rem")=some (.val (.word remnant)):=remE
  have spillValue : eval second spillUsedExpression=some (.val (.word (spill+remnant))) := by
    simp only [eval] at spillRead ⊢
    simp only [spillUsedExpression,evalHOLExact,evalListHOLExact,spillRead]
    simp [evalHOLExact,toExact,localVar,remS,valueIsWord,valueWord,wordOpHOL,wordOp]
  have thirdRun:=WitnessRadix.StoreWord.execute second (frameAddress 192#64) spillUsedExpression (frame+192#64) (spill+remnant)
    (address_read second frame 192#64 pools.ev) spillValue (pools.mapped 192 (by simp))
  let third:={second with memory:=WitnessRadix.StoreWord.put second.memory (frame+192#64) (spill+remnant)}
  have returned : evaluateHOLFiniteState third returnZero=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite third) := by
    simp [returnZero,evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have actual : evaluateHOLFiniteState entered spillTail=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite third) := by
    rw [spillTail,WitnessRadix.StateSteps.next_sequence entered first _ _ firstRun (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence first second _ _ secondRun (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence second third _ _ thirdRun (Nat.le_refl _)]
    exact returned
  refine ⟨restore source "rem" (emptyLocalsHOLFinite third),?_,rfl,rfl⟩
  rw [spillCode]
  exact Input.ScalarScope.declare_execute source _ "rem" remainderExpression remnant spillTail _ remRead actual

end InitECandidate.Solver.GasBudget.StateCharge

#print axioms InitECandidate.Solver.GasBudget.StateCharge.spill_execute
