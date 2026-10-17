import InitECandidate.Solver.GasBudget.ChildErrorCall

namespace InitECandidate.Solver.GasBudget.RegularCharge
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_charge_gas with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "amount",.one)]
def test : ExpHOL 64 := .cmp .lower (localVar "gl") (localVar "amount")
def guard : ProgHOL 64 := .ite test (.raise (ofString "EvmErr") (.const 4#64)) .skip
def gasExpression : ExpHOL 64 := .op .sub [localVar "gl",localVar "amount"]
def usedExpression : ExpHOL 64 := .op .add [frameLoad 184#64,localVar "amount"]
def afterGuard : ProgHOL 64 := .seq (.store (frameAddress 64#64) gasExpression)
  (.seq (.store (frameAddress 184#64) usedExpression) (.return (.const 0#64)))
def tail : ProgHOL 64 := .seq guard afterGuard
def writes (frame gas used amount : BitVec 64) : List (BitVec 64×BitVec 64) :=
  [(frame+64#64,gas-amount),(frame+184#64,used+amount)]

theorem body_shape : body=.dec (ofString "gl") .one (frameLoad 64#64) tail := by
  simp only [body,Guest.guestFn_charge_gas,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    tail,guard,test,afterGuard,gasExpression,usedExpression,frameLoad,frameAddress,localVar]

/-- Source-level counterpart of the already checked Stack charge summary:
the actual affordable charge moves gas from liquid to used, with no body call. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas used amount : BitVec 64)
    (ev : source.globals.lookup (ofString "ev")=some (.val (.word frame)))
    (amountLocal : source.locals.lookup (ofString "amount")=some (.val (.word amount)))
    (gasMapped : source.memaddrs (frame+64#64)) (usedMapped : source.memaddrs (frame+184#64))
    (gasCell : source.memory (frame+64#64)=.word gas) (usedCell : source.memory (frame+184#64)=.word used)
    (affordable : amount≤gas) :
    ∃ target,evaluateHOLFiniteState source body=(some (.returned (.val (.word 0#64))),target) ∧
      target.memory=WitnessRadix.WordWrites.write source.memory (writes frame gas used amount) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory} := by
  classical
  have gasRead:=frame_read source frame 64#64 gas ev gasMapped gasCell
  let entered:=bind source "gl" gas
  have gasE : entered.locals.lookup (ofString "gl")=some (.val (.word gas)):=bind_lookup_same _ _ _
  have amountE : entered.locals.lookup (ofString "amount")=some (.val (.word amount)):=
    (bind_lookup_other _ "gl" "amount" _ (by decide)).trans amountLocal
  have noFailure : ¬gas<amount := by change amount.toNat≤gas.toNat at affordable; change ¬gas.toNat<amount.toNat; omega
  have guardRun : evaluateHOLFiniteState entered guard=(none,entered) := by
    rw [guard,evaluateHOLFiniteState_ite]
    simp [test,evalHOLExact,toExact,localVar,gasE,amountE,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,noFailure]
  have gasValue : eval entered gasExpression=some (.val (.word (gas-amount))) := by
    simp [eval,gasExpression,evalHOLExact,evalListHOLExact,toExact,localVar,gasE,amountE,valueIsWord,valueWord,wordOpHOL,wordOp]
  have firstRun:=WitnessRadix.StoreWord.execute entered (frameAddress 64#64) gasExpression (frame+64#64) (gas-amount)
    (address_read entered frame 64#64 ev) gasValue gasMapped
  let first:={entered with memory:=WitnessRadix.StoreWord.put entered.memory (frame+64#64) (gas-amount)}
  have usedFirst : first.memory (frame+184#64)=.word used:=ChildError.stored_away source.memory _ _ _ _
    (offsets_ne frame 184#64 64#64 (by decide)) usedCell
  have usedRead:=frame_read first frame 184#64 used ev usedMapped usedFirst
  have amountF : first.locals.lookup (ofString "amount")=some (.val (.word amount)):=amountE
  have usedValue : eval first usedExpression=some (.val (.word (used+amount))) := by
    simp only [eval] at usedRead ⊢
    simp only [usedExpression,evalHOLExact,evalListHOLExact,usedRead]
    simp [evalHOLExact,toExact,localVar,amountF,valueIsWord,valueWord,wordOpHOL,wordOp]
  have secondRun:=WitnessRadix.StoreWord.execute first (frameAddress 184#64) usedExpression (frame+184#64) (used+amount)
    (address_read first frame 184#64 ev) usedValue usedMapped
  let second:={first with memory:=WitnessRadix.StoreWord.put first.memory (frame+184#64) (used+amount)}
  have returned : evaluateHOLFiniteState second (.return (.const 0#64))=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite second) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have tailRun : evaluateHOLFiniteState entered tail=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite second) := by
    rw [tail,WitnessRadix.StateSteps.next_sequence entered entered _ _ guardRun (Nat.le_refl _),afterGuard,
      WitnessRadix.StateSteps.next_sequence entered first _ _ firstRun (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence first second _ _ secondRun (Nat.le_refl _)]
    exact returned
  refine ⟨restore source "gl" (emptyLocalsHOLFinite second),?_,rfl,rfl⟩
  rw [body_shape]
  exact Input.ScalarScope.declare_execute source _ "gl" (frameLoad 64#64) gas tail _ gasRead tailRun

theorem failed (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas amount : BitVec 64)
    (ev : source.globals.lookup (ofString "ev")=some (.val (.word frame)))
    (amountLocal : source.locals.lookup (ofString "amount")=some (.val (.word amount)))
    (gasMapped : source.memaddrs (frame+64#64)) (gasCell : source.memory (frame+64#64)=.word gas)
    (unaffordable : gas<amount) (exceptionShape : source.eshapes.lookup (ofString "EvmErr")=some .one) :
    ∃ target,evaluateHOLFiniteState source body=(some (.exception (ofString "EvmErr") (.val (.word 4#64))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite source := by
  classical
  have gasRead:=frame_read source frame 64#64 gas ev gasMapped gasCell
  let entered:=bind source "gl" gas
  have gasE : entered.locals.lookup (ofString "gl")=some (.val (.word gas)):=bind_lookup_same _ _ _
  have amountE : entered.locals.lookup (ofString "amount")=some (.val (.word amount)):=
    (bind_lookup_other _ "gl" "amount" _ (by decide)).trans amountLocal
  have raised : evaluateHOLFiniteState entered (.raise (ofString "EvmErr") (.const 4#64))=
      (some (.exception (ofString "EvmErr") (.val (.word 4#64))),emptyLocalsHOLFinite entered) := by
    have shapeE : entered.eshapes.lookup (ofString "EvmErr")=some .one:=exceptionShape
    simp [evaluateHOLFiniteState_raise,shapeE,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have guardRun : evaluateHOLFiniteState entered guard=
      (some (.exception (ofString "EvmErr") (.val (.word 4#64))),emptyLocalsHOLFinite entered) := by
    rw [guard,evaluateHOLFiniteState_ite]
    simpa [test,evalHOLExact,toExact,localVar,gasE,amountE,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,unaffordable] using raised
  have tailRun : evaluateHOLFiniteState entered tail=
      (some (.exception (ofString "EvmErr") (.val (.word 4#64))),emptyLocalsHOLFinite entered) := by
    rw [tail,WitnessRadix.StateSteps.stopped_sequence entered (emptyLocalsHOLFinite entered) _ _ _ guardRun (Nat.le_refl _)]
  refine ⟨restore source "gl" (emptyLocalsHOLFinite entered),?_,rfl⟩
  rw [body_shape]
  exact Input.ScalarScope.declare_execute source _ "gl" (frameLoad 64#64) gas tail _ gasRead tailRun

end InitECandidate.Solver.GasBudget.RegularCharge

#print axioms InitECandidate.Solver.GasBudget.RegularCharge.body_shape
#print axioms InitECandidate.Solver.GasBudget.RegularCharge.execute
#print axioms InitECandidate.Solver.GasBudget.RegularCharge.failed
