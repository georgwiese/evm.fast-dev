import InitECandidate.Solver.Input.LoopSummaryInvariant
import InitECandidate.Solver.Input.LoopNormalExit
import InitECandidate.Solver.Input.ClockCostLoop
import InitECandidate.Solver.Input.PureReturn
import InitECandidate.Solver.Input.CallResume
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.LocalPrefix
import InitECandidate.Solver.Input.UDivMod.Built
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.WordPairConstCost

namespace InitECandidate.Solver.Input.UDivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Nonzero division covers every clock, including an insufficient loop
clock. Its actual64-round software loop supplies the bound. -/
theorem nonzero_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (aLocal : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b")=some (.val (.word b))) (nonzero : b≠0#64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤64 := by
  by_cases enough : 64≤source.clock
  · obtain ⟨target,q,r,paid,bound,run,clock,frame,arithmetic⟩:=body_execute_nonzero source a b aLocal bLocal nonzero enough
    rw [run,clock]
    omega
  · omega

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "udivmod")=some (formals,body,returnShape) := by
  have checked:=OriginalCode.indexed code installed 28 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_udivmod) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,returnShape,
    Guest.Software.guestFn_udivmod,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

namespace Divide

def body : ProgHOL 64 := match Guest.Software.guestFn_udiv with | .function fn=>progToHOL fn.body | _=>.skip
def tail : ProgHOL 64 := .return (.rfield 0 (localVar "qr"))

theorem shape : body=.decCall (ofString "qr") returnShape (ofString "udivmod") [localVar "a",localVar "b"] tail := by
  simp only [body,tail,returnShape,Guest.Software.guestFn_udiv,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "udiv")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 29 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_udiv) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_udiv,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- Actual scalar division, including its scoped udivmod ABI, needs at
most65 source ticks for every nonzero divisor. -/
theorem nonzero_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (aLocal : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b")=some (.val (.word b))) (nonzero : b≠0#64)
    (code : source.code.lookup (ofString "udivmod")=some (formals,UDivMod.body,returnShape)) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤65 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "a",localVar "b"]=some [.val (.word a),.val (.word b)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,aLocal,bLocal]
  obtain ⟨callee,called,aCell,bCell⟩:=word_pair_environment source.code.lookup (ofString "udivmod") (ofString "a") (ofString "b") UDivMod.body returnShape a b (by decide) code
  rw [shape]
  exact ClockCost.scoped_current source (ofString "qr") returnShape (ofString "udivmod") [localVar "a",localVar "b"] _ UDivMod.body tail callee returnShape 64 0 args called
    (UDivMod.nonzero_cost (callEntryStateHOLFinite source callee) a b aCell bCell nonzero)
    (ClockCost.returned source.code _)

end Divide
end InitECandidate.Solver.Input.UDivMod

#print axioms InitECandidate.Solver.Input.UDivMod.nonzero_cost
#print axioms InitECandidate.Solver.Input.UDivMod.original_code
#print axioms InitECandidate.Solver.Input.UDivMod.Divide.original_code
#print axioms InitECandidate.Solver.Input.UDivMod.Divide.nonzero_cost


namespace InitECandidate.Solver.Input.UDivMod.Div64By32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_div64by32 with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "hi",.one),(ofString "lo",.one),(ofString "d",.one)]
def remainderExpression : ExpHOL 64:=.op .or [
  .shift .lsl (localVar "r") (.const 1#64),
  .op .and [.shift .lsr (localVar "lo") (localVar "i"),.const 1#64]]
def subtractTest : ExpHOL 64:=.cmp .notLower (localVar "r") (localVar "d")
def subtractExpression : ExpHOL 64:=.op .sub [localVar "r",localVar "d"]
def subtractBody : ProgHOL 64:=.seq (.assign .local (ofString "r") subtractExpression) (.assign .local (ofString "q") quotientExpression)
def loopBody : ProgHOL 64:=.seq (.assign .local (ofString "i") indexExpression)
  (.seq (.assign .local (ofString "r") remainderExpression) (.ite subtractTest subtractBody .skip))
def loop : ProgHOL 64:=.while loopTest loopBody
def initializedBody : ProgHOL 64:=.seq loop returnPair
def setupProgram : ProgHOL 64:=.dec (ofString "q") .one (.const 0#64)
  (.dec (ofString "r") .one (localVar "hi") (.dec (ofString "i") .one (.const 32#64) initializedBody))

theorem body_shape : body=setupProgram := by
  simp only [body,Guest.Software.guestFn_div64by32,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    setupProgram,initializedBody,loop,loopTest,loopBody,indexExpression,remainderExpression,subtractTest,subtractBody,
    subtractExpression,quotientExpression,returnPair,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "div64by32")=some (formals,body,returnShape) := by
  have checked:=OriginalCode.indexed code installed 57 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_div64by32) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,returnShape,
    Guest.Software.guestFn_div64by32,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b q r : BitVec 64) (index : Nat)
    (positive : 0<index) (small : index≤64)
    (aLocal : source.locals.lookup (ofString "lo")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "d")=some (.val (.word b)))
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
  have aFirst : first.locals.lookup (ofString "lo")=some (.val (.word a)) := (bind_lookup_other source "i" "lo" _ (by decide)).trans aLocal
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
  have bSecond : second.locals.lookup (ofString "d")=some (.val (.word b)) :=
    (bind_lookup_other first "r" "d" _ (by decide)).trans ((bind_lookup_other source "i" "d" _ (by decide)).trans bLocal)
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


/-- The actual division loop always finishes within its remaining at-most64
rounds. This statement accounts for execution and frames; it does not assume
or assert arithmetic division correctness. -/
theorem loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b q r : BitVec 64) (total index : Nat)
    (small : index≤64) (enough : index≤source.clock)
    (aLocal : source.locals.lookup (ofString "lo")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "d")=some (.val (.word b)))
    (qLocal : source.locals.lookup (ofString "q")=some (.val (.word q)))
    (rLocal : source.locals.lookup (ofString "r")=some (.val (.word r)))
    (iLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    ∃ target finalQ finalR,
      evaluateHOLFiniteState source loop=(none,target) ∧
      target={source with locals:=target.locals,clock:=source.clock-index} ∧
      target.locals.lookup (ofString "i")=some (.val (.word 0#64)) ∧
      target.locals.lookup (ofString "q")=some (.val (.word finalQ)) ∧
      target.locals.lookup (ofString "r")=some (.val (.word finalR)) ∧
      (∀ name : MlS,name≠ofString "i"→name≠ofString "q"→name≠ofString "r"→target.locals.lookup name=source.locals.lookup name) ∧
      (∀ bSmall : b.toNat≤2^63,SeededArithmetic a b q r total index→SeededArithmetic a b finalQ finalR total 0) := by
  classical
  induction index generalizing source q r with
  | zero=>
    have test : evalHOLFinite source loopTest=some (.val (.word 0#64)) := by
      rw [finite_eval]
      simpa only [eval,Nat.lt_irrefl,↓reduceIte] using loop_test source 0 (by decide) iLocal
    refine ⟨source,q,r,?_,by simp, iLocal,qLocal,rLocal,(by intros; rfl),(by intro bSmall invariant; exact invariant)⟩
    rw [loop,evaluateHOLFiniteState_while_total,test]
    simp
  | succ index ih=>
    let entry:=decClockHOLFinite source
    let next:=step entry a b q r (index+1)
    have nextState : next={entry with locals:=next.locals}:=step_state entry a b q r (index+1)
    have nextClock : next.clock=source.clock-1:=congrArg PanSemStateFiniteExact.clock nextState
    have bodyRun:=body_execute entry a b q r (index+1) (by omega) small aLocal bLocal qLocal rLocal iLocal
    have fields:=step_fields entry a b q r (index+1) qLocal
    have nextA : next.locals.lookup (ofString "lo")=some (.val (.word a)) :=
      (step_other entry a b q r (index+1) (ofString "lo") (by decide) (by decide) (by decide)).trans aLocal
    have nextB : next.locals.lookup (ofString "d")=some (.val (.word b)) :=
      (step_other entry a b q r (index+1) (ofString "d") (by decide) (by decide) (by decide)).trans bLocal
    obtain ⟨target,finalQ,finalR,tailRun,targetState,finalI,finalQRead,finalRRead,others,arithmetic⟩:=
      ih next (nextQ a b q r (index+1)) (nextR a b r (index+1)) (by omega) (by omega) nextA nextB fields.2.1 fields.2.2 (by simpa using fields.1)
    have targetClock : target.clock=next.clock-index:=congrArg PanSemStateFiniteExact.clock targetState
    have targetClockBound : target.clock≤source.clock-1 := by omega
    have test : evalHOLFinite source loopTest=some (.val (.word 1#64)) := by
      rw [finite_eval]
      simpa only [eval,show 0<index+1 from by omega,↓reduceIte] using loop_test source (index+1) small iLocal
    refine ⟨target,finalQ,finalR,?_,?_,finalI,finalQRead,finalRRead,?_,?_⟩
    · rw [loop,evaluateHOLFiniteState_while_total,test]
      simp only []
      simp only [if_neg (show source.clock≠0 by omega)]
      rw [bodyRun,WitnessRadix.StateSteps.fixed_clock entry next none (by change next.clock≤source.clock-1; omega)]
      simp only []
      split
      · exact tailRun
      · rename_i impossible
        exact (impossible (by decide)).elim
    · rw [nextState] at targetState
      change target={source with locals:=target.locals,clock:=source.clock-1-index} at targetState
      have subtract : source.clock-1-index=source.clock-(index+1) := by omega
      simpa only [subtract] using targetState
    · intro name notI notQ notR
      exact (others name notI notQ notR).trans (step_other entry a b q r (index+1) name notI notQ notR)
    · intro bSmall invariant
      exact arithmetic bSmall (seeded_step a b q r total index (by omega) bSmall invariant)

theorem setup_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (high a b : BitVec 64)
    (highLocal : source.locals.lookup (ofString "hi")=some (.val (.word high)))
    (aLocal : source.locals.lookup (ofString "lo")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "d")=some (.val (.word b))) (enough : 32≤source.clock) :
    ∃ target q r,evaluateHOLFiniteState source setupProgram=(some (.returned (pairValue q r)),target) ∧
      target.clock=source.clock-32 ∧ frozen target=frozen source ∧
      (∀ bSmall : b.toNat≤2^63,high.toNat<b.toNat→a.toNat<2^32→
        q.toNat=(high.toNat*2^32+a.toNat)/b.toNat ∧ r.toNat=(high.toNat*2^32+a.toNat)%b.toNat) := by
  classical
  let q0:=bind source "q" 0#64
  let r0:=bind q0 "r" high
  let entry:=bind r0 "i" 32#64
  have aEntry : entry.locals.lookup (ofString "lo")=some (.val (.word a)) :=
    (bind_lookup_other r0 "i" "lo" _ (by decide)).trans ((bind_lookup_other q0 "r" "lo" _ (by decide)).trans
      ((bind_lookup_other source "q" "lo" _ (by decide)).trans aLocal))
  have bEntry : entry.locals.lookup (ofString "d")=some (.val (.word b)) :=
    (bind_lookup_other r0 "i" "d" _ (by decide)).trans ((bind_lookup_other q0 "r" "d" _ (by decide)).trans
      ((bind_lookup_other source "q" "d" _ (by decide)).trans bLocal))
  have qEntry : entry.locals.lookup (ofString "q")=some (.val (.word 0#64)) :=
    (bind_lookup_other r0 "i" "q" _ (by decide)).trans ((bind_lookup_other q0 "r" "q" _ (by decide)).trans (bind_lookup_same source "q" _))
  have rEntry : entry.locals.lookup (ofString "r")=some (.val (.word high)) :=
    (bind_lookup_other r0 "i" "r" _ (by decide)).trans (bind_lookup_same q0 "r" _)
  have iEntry : entry.locals.lookup (ofString "i")=some (.val (.word 32#64)) := bind_lookup_same r0 "i" _
  obtain ⟨loopPost,q,r,loopRun,loopEq,finalI,finalQ,finalR,others,arithmetic⟩:=loop_execute entry a b 0#64 high (high.toNat*2^32+a.toNat) 32 (by decide) enough aEntry bEntry qEntry rEntry iEntry
  have loopClock : loopPost.clock=source.clock-32:=congrArg PanSemStateFiniteExact.clock loopEq
  have returnRun : evaluateHOLFiniteState loopPost returnPair=(some (.returned (pairValue q r)),emptyLocalsHOLFinite loopPost) := by
    simp [returnPair,pairValue,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,finalQ,finalR,
      shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have enteredRun : evaluateHOLFiniteState entry initializedBody=(some (.returned (pairValue q r)),emptyLocalsHOLFinite loopPost) := by
    rw [initializedBody,WitnessRadix.StateSteps.next_sequence entry loopPost _ _ loopRun (by change loopPost.clock≤source.clock; omega)]
    exact returnRun
  have iRun:=ScalarScope.declare_execute r0 (emptyLocalsHOLFinite loopPost) "i" (.const 32#64) 32#64 initializedBody
    (some (.returned (pairValue q r))) rfl enteredRun
  have highRead : eval q0 (localVar "hi")=some (.val (.word high)):=by
    have highQ : q0.locals.lookup (ofString "hi")=some (.val (.word high)):=(bind_lookup_other source "q" "hi" 0#64 (by decide)).trans highLocal
    simp [eval,localVar,evalHOLExact,toExact,highQ]
  have rRun:=ScalarScope.declare_execute q0 (restore r0 "i" (emptyLocalsHOLFinite loopPost)) "r" (localVar "hi") high
    (.dec (ofString "i") .one (.const 32#64) initializedBody) (some (.returned (pairValue q r))) highRead iRun
  have qRun:=ScalarScope.declare_execute source (restore q0 "r" (restore r0 "i" (emptyLocalsHOLFinite loopPost))) "q" (.const 0#64) 0#64
    (.dec (ofString "r") .one (localVar "hi") (.dec (ofString "i") .one (.const 32#64) initializedBody))
    (some (.returned (pairValue q r))) rfl rRun
  refine ⟨_,q,r,qRun,loopClock,?_,?_⟩
  · change frozen loopPost=frozen source
    rw [loopEq]
    rfl
  · intro bSmall highSmall lowSmall
    exact seeded_finish a b q r (high.toNat*2^32+a.toNat) (arithmetic bSmall (seeded_initial32 a high b lowSmall highSmall))


theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (high low divisor : BitVec 64)
    (highLocal : source.locals.lookup (ofString "hi")=some (.val (.word high)))
    (lowLocal : source.locals.lookup (ofString "lo")=some (.val (.word low)))
    (divisorLocal : source.locals.lookup (ofString "d")=some (.val (.word divisor))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤32 := by
  by_cases enough : 32≤source.clock
  · obtain ⟨target,q,r,run,clock,frame,arithmetic⟩:=setup_execute source high low divisor highLocal lowLocal divisorLocal enough
    rw [body_shape,run,clock]
    omega
  · omega

/-- A normally completed actual loop derives its own remaining funding. -/
theorem loop_funded (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b q r : BitVec 64) (index : Nat)
    (small : index≤64)
    (aLocal : source.locals.lookup (ofString "lo")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "d")=some (.val (.word b)))
    (qLocal : source.locals.lookup (ofString "q")=some (.val (.word q)))
    (rLocal : source.locals.lookup (ofString "r")=some (.val (.word r)))
    (iLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (normal : evaluateHOLFiniteState source loop=(none,post)) : index≤source.clock := by
  classical
  induction index generalizing source q r with
  | zero=>omega
  | succ index ih=>
    let entry:=decClockHOLFinite source
    let next:=step entry a b q r (index+1)
    have nextState : next={entry with locals:=next.locals}:=step_state entry a b q r (index+1)
    have nextClock : next.clock=source.clock-1:=congrArg PanSemStateFiniteExact.clock nextState
    have bodyRun:=body_execute entry a b q r (index+1) (by omega) small aLocal bLocal qLocal rLocal iLocal
    have fields:=step_fields entry a b q r (index+1) qLocal
    have nextA : next.locals.lookup (ofString "lo")=some (.val (.word a)):=
      (step_other entry a b q r (index+1) (ofString "lo") (by decide) (by decide) (by decide)).trans aLocal
    have nextB : next.locals.lookup (ofString "d")=some (.val (.word b)):=
      (step_other entry a b q r (index+1) (ofString "d") (by decide) (by decide) (by decide)).trans bLocal
    have test : evalHOLFinite source loopTest=some (.val (.word 1#64)):=by
      rw [finite_eval]
      simpa only [eval,show 0<index+1 from by omega,↓reduceIte] using loop_test source (index+1) small iLocal
    rw [loop,evaluateHOLFiniteState_while_total,test] at normal
    simp only [show (1#64 : BitVec 64)≠0#64 by decide,↓reduceIte] at normal
    by_cases zero : source.clock=0
    · rw [if_pos zero] at normal
      cases normal
    · rw [if_neg zero,bodyRun,WitnessRadix.StateSteps.fixed_clock entry next none (by change next.clock≤source.clock-1;omega)] at normal
      have tail : evaluateHOLFiniteState next loop=(none,post):=normal
      have funded:=ih next (nextQ a b q r (index+1)) (nextR a b r (index+1)) (by omega) nextA nextB fields.2.1 fields.2.2
        (by simpa using fields.1) tail
      rw [nextClock] at funded
      omega


theorem loop_safe : LocalPrefix (ofString "lo") loop := by
  unfold loop loopBody subtractBody
  exact .loop _ (.seq (.assign _ _ (by decide)) (.seq (.assign _ _ (by decide))
    (.ite _ (.seq (.assign _ _ (by decide)) (.assign _ _ (by decide))) .skip)))

/-- Successful execution derives all32body ticks and the actual quotient
and remainder. Its arithmetic hypotheses concern the real incoming words. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (high a b : BitVec 64)
    (highLocal : source.locals.lookup (ofString "hi")=some (.val (.word high)))
    (aLocal : source.locals.lookup (ofString "lo")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "d")=some (.val (.word b)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    ∃ q r,returned=pairValue q r ∧ 32≤source.clock ∧ post.clock=source.clock-32 ∧ frozen post=frozen source ∧
      (∀ bSmall : b.toNat≤2^63,high.toNat<b.toNat→a.toNat<2^32→
        q.toNat=(high.toNat*2^32+a.toNat)/b.toNat ∧ r.toNat=(high.toNat*2^32+a.toNat)%b.toNat) := by
  classical
  have saved:=normal
  rw [body_shape,setupProgram] at normal
  obtain ⟨postQ,qRun,qRestore⟩:=declaration_return_word source post "q" (.const 0#64) 0#64
    (.dec (ofString "r") .one (localVar "hi") (.dec (ofString "i") .one (.const 32#64) initializedBody)) returned rfl normal
  let q0:=bind source "q" 0#64
  let r0:=bind q0 "r" high
  let entry:=bind r0 "i" 32#64
  have highQ : q0.locals.lookup (ofString "hi")=some (.val (.word high)):=
    (bind_lookup_other source "q" "hi" 0#64 (by decide)).trans highLocal
  have highRead : eval q0 (localVar "hi")=some (.val (.word high)):=by
    simp [eval,localVar,evalHOLExact,toExact,highQ]
  obtain ⟨postR,rRun,rRestore⟩:=declaration_return_word q0 postQ "r" (localVar "hi") high
    (.dec (ofString "i") .one (.const 32#64) initializedBody) returned highRead qRun
  obtain ⟨postI,enteredRun,iRestore⟩:=declaration_return_word r0 postR "i" (.const 32#64) 32#64 initializedBody returned rfl rRun
  change evaluateHOLFiniteState entry initializedBody=(some (.returned returned),postI) at enteredRun
  have aEntry : entry.locals.lookup (ofString "lo")=some (.val (.word a)) :=
    (bind_lookup_other r0 "i" "lo" _ (by decide)).trans ((bind_lookup_other q0 "r" "lo" _ (by decide)).trans
      ((bind_lookup_other source "q" "lo" _ (by decide)).trans aLocal))
  have bEntry : entry.locals.lookup (ofString "d")=some (.val (.word b)) :=
    (bind_lookup_other r0 "i" "d" _ (by decide)).trans ((bind_lookup_other q0 "r" "d" _ (by decide)).trans
      ((bind_lookup_other source "q" "d" _ (by decide)).trans bLocal))
  have qEntry : entry.locals.lookup (ofString "q")=some (.val (.word 0#64)) :=
    (bind_lookup_other r0 "i" "q" _ (by decide)).trans ((bind_lookup_other q0 "r" "q" _ (by decide)).trans (bind_lookup_same source "q" _))
  have rEntry : entry.locals.lookup (ofString "r")=some (.val (.word high)) :=
    (bind_lookup_other r0 "i" "r" _ (by decide)).trans (bind_lookup_same q0 "r" _)
  have iEntry : entry.locals.lookup (ofString "i")=some (.val (.word 32#64)) := bind_lookup_same r0 "i" _
  obtain ⟨loopPost,loopRun,returnRun⟩:=sequence_returned entry postI loop returnPair returned (loop_safe.summary entry).2 enteredRun
  have enough : 32≤source.clock:=loop_funded entry loopPost a b 0#64 high 32 (by decide) aEntry bEntry qEntry rEntry iEntry loopRun
  obtain ⟨target,q,r,run,clock,frame,arithmetic⟩:=setup_execute source high a b highLocal aLocal bLocal enough
  rw [←body_shape] at run
  have same:=saved.symm.trans run
  have result : returned=pairValue q r:=by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using congrArg Prod.fst same
  have postEq : post=target:=congrArg Prod.snd same
  exact ⟨q,r,result,enough,postEq ▸ clock,postEq ▸ frame,arithmetic⟩


/-- Real valid digit inputs produce digit-sized quotient/remainder words. -/
theorem body_normal_digits (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (high low divisor : BitVec 64)
    (highLocal : source.locals.lookup (ofString "hi")=some (.val (.word high)))
    (lowLocal : source.locals.lookup (ofString "lo")=some (.val (.word low)))
    (divisorLocal : source.locals.lookup (ofString "d")=some (.val (.word divisor)))
    (divisorSmall : divisor.toNat<2^32) (highSmall : high.toNat<divisor.toNat) (lowSmall : low.toNat<2^32)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    ∃ q r,returned=pairValue q r ∧ 32≤source.clock ∧ post.clock=source.clock-32 ∧ frozen post=frozen source ∧
      q.toNat=(high.toNat*2^32+low.toNat)/divisor.toNat ∧ r.toNat=(high.toNat*2^32+low.toNat)%divisor.toNat ∧
      q.toNat<2^32 ∧ r.toNat<divisor.toNat := by
  obtain ⟨q,r,result,funded,clock,frame,arithmetic⟩:=body_normal source post high low divisor highLocal lowLocal divisorLocal returned normal
  obtain ⟨quotient,remainder⟩:=arithmetic (by omega) highSmall lowSmall
  have positive : 0<divisor.toNat:=by omega
  have dividendBound : high.toNat*2^32+low.toNat<2^32*divisor.toNat:=by nlinarith
  have quotientBound : q.toNat<2^32:=by
    rw [quotient,Nat.div_lt_iff_lt_mul positive]
    exact dividendBound
  have remainderBound : r.toNat<divisor.toNat:=by
    rw [remainder]
    exact Nat.mod_lt _ positive
  exact ⟨q,r,result,funded,clock,frame,quotient,remainder,quotientBound,remainderBound⟩

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (high low divisor : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word high),.val (.word low),.val (.word divisor)])
    (tailBound : ClockCost.Bound source.code continuation tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) returnShape (ofString "div64by32") arguments continuation)).2.clock≤
      32+tailPrice+1 := by
  obtain ⟨callee,called,highCell,lowCell,divisorCell⟩:=word_triple_environment source.code.lookup (ofString "div64by32")
    (ofString "hi") (ofString "lo") (ofString "d") body returnShape high low divisor (by decide) (by decide) (by decide) (original_code source.code installed)
  exact ClockCost.scoped_current source (ofString name) returnShape (ofString "div64by32") arguments _ body continuation callee returnShape 32 tailPrice args called
    (body_cost (callEntryStateHOLFinite source callee) high low divisor highCell lowCell divisorCell) tailBound

/-- Actual current three-scalar callee return derives its numerical result,
funding and canonical caller state. -/
theorem resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (high low divisor : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (divisorSmall : divisor.toNat<2^32) (highSmall : high.toNat<divisor.toNat) (lowSmall : low.toNat<2^32)
    (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "div64by32")
      [.val (.word high),.val (.word low),.val (.word divisor)]=some (actual,callee,shape))
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual=(some (.returned returned),target)) :
    ∃ q r,returned=pairValue q r ∧ 33≤source.clock ∧ q.toNat=(high.toNat*2^32+low.toNat)/divisor.toNat ∧
      r.toNat=(high.toNat*2^32+low.toNat)%divisor.toNat ∧ q.toNat<2^32 ∧ r.toNat<divisor.toNat ∧
      CallNormal.continuationEntry source target name returned=
        setVarHOLFinite (ofString name) (pairValue q r) {source with clock:=source.clock-33} := by
  obtain ⟨expected,lookup,highCell,lowCell,divisorCell⟩:=word_triple_environment source.code.lookup (ofString "div64by32")
    (ofString "hi") (ofString "lo") (ofString "d") body returnShape high low divisor (by decide) (by decide) (by decide) (original_code source.code installed)
  have same:=Option.some.inj (called.symm.trans lookup)
  have bodyEq : actual=body:=congrArg Prod.fst same
  have calleeEq : callee=expected:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  rw [←calleeEq] at highCell lowCell divisorCell
  rw [bodyEq] at run
  obtain ⟨q,r,result,funded,clock,frame,quotient,remainder,quotientBound,remainderBound⟩:=
    body_normal_digits (callEntryStateHOLFinite source callee) target high low divisor highCell lowCell divisorCell divisorSmall highSmall lowSmall returned run
  have more : 32≤source.clock-1:=funded
  have targetClock : target.clock=source.clock-33:=by
    change target.clock=source.clock-1-32 at clock
    simpa only [Nat.sub_sub] using clock
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals,clock:=target.clock}) frame
  change {target with locals:=source.locals}={source with clock:=target.clock} at callerFrame
  have canonical : {target with locals:=source.locals}={source with clock:=source.clock-33}:=
    callerFrame.trans (congrArg (fun paid : Nat=>{source with clock:=paid}) targetClock)
  exact ⟨q,r,result,by omega,quotient,remainder,quotientBound,remainderBound,
    by simp only [CallNormal.continuationEntry,result,canonical]⟩

end InitECandidate.Solver.Input.UDivMod.Div64By32

#print axioms InitECandidate.Solver.Input.UDivMod.Div64By32.body_shape
#print axioms InitECandidate.Solver.Input.UDivMod.Div64By32.original_code
#print axioms InitECandidate.Solver.Input.UDivMod.Div64By32.body_execute
#print axioms InitECandidate.Solver.Input.UDivMod.Div64By32.loop_execute

#print axioms InitECandidate.Solver.Input.UDivMod.Div64By32.setup_execute
#print axioms InitECandidate.Solver.Input.UDivMod.Div64By32.body_cost
#print axioms InitECandidate.Solver.Input.UDivMod.Div64By32.loop_funded

#print axioms InitECandidate.Solver.Input.UDivMod.Div64By32.loop_safe
#print axioms InitECandidate.Solver.Input.UDivMod.Div64By32.body_normal

#print axioms InitECandidate.Solver.Input.UDivMod.Div64By32.body_normal_digits
#print axioms InitECandidate.Solver.Input.UDivMod.Div64By32.call_cost
#print axioms InitECandidate.Solver.Input.UDivMod.Div64By32.resume

namespace InitECandidate.Solver.Input.UDivMod.Nlz32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

private theorem mask_test (value mask : BitVec 64) (bits : Nat)
    (valueSmall : value.toNat<2^32) (bitsSmall : bits≤32)
    (partition : (BitVec.ofNat 64 (2^bits-1)) ||| mask=4294967295#64)
    (disjoint : (BitVec.ofNat 64 (2^bits-1)) &&& mask=0#64) :
    value &&& mask=0#64 ↔ value.toNat<2^bits := by
  have power : 2^bits≤2^32:=Nat.pow_le_pow_right (by decide) bitsSmall
  have lowNumber : (BitVec.ofNat 64 (2^bits-1)).toNat=2^bits-1:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have lowHalf : (value &&& (BitVec.ofNat 64 (2^bits-1))).toNat=value.toNat%2^bits:=by
    rw [BitVec.toNat_and,lowNumber,Nat.and_two_pow_sub_one_eq_mod]
  have allHalf : value &&& 4294967295#64=value:=by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    change value.toNat &&& (2^32-1)=value.toNat
    rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt valueSmall]
  constructor
  · intro zero
    have joined : value=(value &&& BitVec.ofNat 64 (2^bits-1)) ||| (value &&& mask):=by
      rw [←BitVec.and_or_distrib_left,partition,allHalf]
    rw [zero,BitVec.or_zero] at joined
    have native:=congrArg BitVec.toNat joined
    rw [lowHalf] at native
    have bound:=Nat.mod_lt value.toNat (Nat.two_pow_pos bits)
    omega
  · intro small
    have lowSame : value &&& (BitVec.ofNat 64 (2^bits-1))=value:=by
      apply BitVec.eq_of_toNat_eq
      rw [lowHalf,Nat.mod_eq_of_lt small]
    calc value &&& mask=(value &&& BitVec.ofNat 64 (2^bits-1)) &&& mask:=
          congrArg (fun word : BitVec 64=>word &&& mask) lowSame.symm
      _=value &&& ((BitVec.ofNat 64 (2^bits-1)) &&& mask):=BitVec.and_assoc _ _ _
      _=0#64:=by rw [disjoint];simp

def mask (amount : Nat) : BitVec 64:=match amount with
  | 16=>4294901760#64 | 8=>4278190080#64 | 4=>4026531840#64 | 2=>3221225472#64 | _=>2147483648#64

theorem mask_zero (value : BitVec 64) (amount : Nat) (allowed : amount=16 ∨ amount=8 ∨ amount=4 ∨ amount=2 ∨ amount=1)
    (valueSmall : value.toNat<2^32) :
    value &&& mask amount=0#64 ↔ value.toNat<2^(32-amount) := by
  apply mask_test value (mask amount) (32-amount) valueSmall (by omega)
  · rcases allowed with rfl|rfl|rfl|rfl|rfl <;> decide
  · rcases allowed with rfl|rfl|rfl|rfl|rfl <;> decide

/-- The conditional shift used at each normalization stage stays within
32bits, raises its known lower bound and conserves the original value. -/
theorem shifted_bounds (value : BitVec 64) (amount : Nat) (positive : 0<amount) (small : 2*amount≤32)
    (lower : 2^(32-2*amount)≤value.toNat) (upper : value.toNat<2^(32-amount)) :
    (value<<<amount).toNat=value.toNat*2^amount ∧
      2^(32-amount)≤(value<<<amount).toNat ∧ (value<<<amount).toNat<2^32 := by
  have powerPos:=Nat.two_pow_pos amount
  have upperProduct:=Nat.mul_lt_mul_of_pos_right upper powerPos
  have lowerProduct:=Nat.mul_le_mul_right (2^amount) lower
  have upperPower : 2^(32-amount)*2^amount=2^32:=by
    rw [←Nat.pow_add,show 32-amount+amount=32 by omega]
  have lowerPower : 2^(32-2*amount)*2^amount=2^(32-amount):=by
    rw [←Nat.pow_add,show 32-2*amount+amount=32-amount by omega]
  rw [upperPower] at upperProduct
  rw [lowerPower] at lowerProduct
  have represented : (value<<<amount).toNat=value.toNat*2^amount:=by
    rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.mod_eq_of_lt (by omega)]
  exact ⟨represented,by rw [represented];exact lowerProduct,by rw [represented];exact upperProduct⟩

end InitECandidate.Solver.Input.UDivMod.Nlz32

#print axioms InitECandidate.Solver.Input.UDivMod.Nlz32.mask_zero
#print axioms InitECandidate.Solver.Input.UDivMod.Nlz32.shifted_bounds

namespace InitECandidate.Solver.Input.UDivMod.Nlz32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_nlz32 with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "x",.one)]
def test (amount : Nat) : ExpHOL 64:=.cmp .equal (.op .and [localVar "x",.const (mask amount)]) (.const 0#64)
def shiftedExpression (amount : Nat) : ExpHOL 64:=.shift .lsl (localVar "x") (.const (BitVec.ofNat 64 amount))
def addition (amount : Nat) : ExpHOL 64:=.op .add [localVar "s",.const (BitVec.ofNat 64 amount)]
def active (amount : Nat) : ProgHOL 64:=.seq (.assign .local (ofString "s") (addition amount)) (.assign .local (ofString "x") (shiftedExpression amount))
def stage (amount : Nat) : ProgHOL 64:=.ite (test amount) (active amount) .skip
def finish : ProgHOL 64:=.seq (.ite (test 1) (.assign .local (ofString "s") (addition 1)) .skip) (.return (localVar "s"))
def stages : List Nat→ProgHOL 64
  | []=>finish
  | amount::rest=>.seq (stage amount) (stages rest)

theorem body_shape : body=.dec (ofString "s") .one (.const 0#64) (stages [16,8,4,2]) := by
  simp only [body,Guest.Software.guestFn_nlz32,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    stages,stage,test,active,shiftedExpression,addition,finish,mask,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "nlz32")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 56 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_nlz32) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_nlz32,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

private theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64) (amount : Nat)
    (x : source.locals.lookup (ofString "x")=some (.val (.word value))) :
    eval source (test amount)=some (.val (.word (if value &&& mask amount=0#64 then 1#64 else 0#64))) := by
  have maskFold : mask amount &&& 18446744073709551615#64=mask amount:=BitVec.and_allOnes
  simp [eval,test,localVar,evalHOLExact,evalListHOLExact,toExact,x,valueIsWord,valueWord,wordOpHOL,wordOp,AndOp.and,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,maskFold]

theorem stage_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (origin value : BitVec 64) (count amount : Nat)
    (allowed : amount=16 ∨ amount=8 ∨ amount=4 ∨ amount=2)
    (valueSmall : value.toNat<2^32) (lower : 2^(32-2*amount)≤value.toNat)
    (conserved : value.toNat=origin.toNat*2^count)
    (x : source.locals.lookup (ofString "x")=some (.val (.word value)))
    (s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 count)))) :
    ∃ target nextValue nextCount,nextCount≤count+amount ∧ 2^(32-amount)≤nextValue.toNat ∧ nextValue.toNat<2^32 ∧
      nextValue.toNat=origin.toNat*2^nextCount ∧ evaluateHOLFiniteState source (stage amount)=(none,target) ∧
      target={source with locals:=target.locals} ∧
      target.locals.lookup (ofString "x")=some (.val (.word nextValue)) ∧
      target.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 nextCount))) := by
  classical
  have amountSmall : amount<64:=by omega
  have positive : 0<amount:=by omega
  have twiceSmall : 2*amount≤32:=by omega
  have amountNumber : (BitVec.ofNat 64 amount).toNat=amount:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have testRead:=test_read source value amount x
  simp only [eval] at testRead
  by_cases take : value &&& mask amount=0#64
  · have upper:=(mask_zero value amount (by tauto) valueSmall).mp take
    obtain ⟨represented,newLower,newUpper⟩:=shifted_bounds value amount positive twiceSmall lower upper
    have newConserved : (value<<<amount).toNat=origin.toNat*2^(count+amount):=by
      rw [represented,conserved,Nat.pow_add,Nat.mul_assoc]
    have addRead : eval source (addition amount)=some (.val (.word (BitVec.ofNat 64 (count+amount)))):=by
      simp [eval,addition,localVar,evalHOLExact,evalListHOLExact,toExact,s,valueIsWord,valueWord,wordOpHOL,wordOp,←BitVec.ofNat_add]
    let added:=bind source "s" (BitVec.ofNat 64 (count+amount))
    have addRun:=WitnessRadix.StateSteps.assign_execute source "s" (addition amount) _ _ s addRead
    have xAdded : added.locals.lookup (ofString "x")=some (.val (.word value)):=
      (bind_lookup_other _ "s" "x" _ (by decide)).trans x
    have shiftedRead : eval added (shiftedExpression amount)=some (.val (.word (value<<<amount))):=by
      simp [eval,shiftedExpression,localVar,evalHOLExact,toExact,xAdded,wordShiftHOL,amountNumber,amountSmall]
    have shiftRun:=WitnessRadix.StateSteps.assign_execute added "x" (shiftedExpression amount) _ _ xAdded shiftedRead
    let target:=bind added "x" (value<<<amount)
    have activeRun : evaluateHOLFiniteState source (active amount)=(none,target):=by
      rw [active,WitnessRadix.StateSteps.next_sequence source added _ _ addRun (Nat.le_refl _)]
      exact shiftRun
    refine ⟨target,value<<<amount,count+amount,by omega,newLower,newUpper,newConserved,?_,rfl,bind_lookup_same _ _ _,?_⟩
    · rw [stage,evaluateHOLFiniteState_ite,testRead]
      simpa only [if_pos take,if_neg (show (1#64 : BitVec 64)≠0 by decide)] using activeRun
    · exact (bind_lookup_other _ "x" "s" _ (by decide)).trans (bind_lookup_same _ _ _)
  · have newLower : 2^(32-amount)≤value.toNat:=by
      have upperNot : ¬value.toNat<2^(32-amount):=fun upper=>take ((mask_zero value amount (by tauto) valueSmall).mpr upper)
      omega
    refine ⟨source,value,count,by omega,newLower,valueSmall,conserved,?_,rfl,x,s⟩
    rw [stage,evaluateHOLFiniteState_ite,testRead]
    simp [take]

end InitECandidate.Solver.Input.UDivMod.Nlz32

#print axioms InitECandidate.Solver.Input.UDivMod.Nlz32.body_shape
#print axioms InitECandidate.Solver.Input.UDivMod.Nlz32.original_code
#print axioms InitECandidate.Solver.Input.UDivMod.Nlz32.stage_execute


namespace InitECandidate.Solver.Input.UDivMod.Nlz32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem finish_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (origin value : BitVec 64) (count : Nat)
    (countSmall : count≤30) (valueSmall : value.toNat<2^32) (lower : 2^30≤value.toNat)
    (conserved : value.toNat=origin.toNat*2^count)
    (x : source.locals.lookup (ofString "x")=some (.val (.word value)))
    (s : source.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 count)))) :
    ∃ bits,bits≤31 ∧ 2^31≤origin.toNat*2^bits ∧ origin.toNat*2^bits<2^32 ∧
      evaluateHOLFiniteState source finish=
        (some (.returned (.val (.word (BitVec.ofNat 64 bits)))),emptyLocalsHOLFinite source) := by
  classical
  have testRead:=test_read source value 1 x
  simp only [eval] at testRead
  by_cases take : value &&& mask 1=0#64
  · have upper:=(mask_zero value 1 (by omega) valueSmall).mp take
    have productEq : origin.toNat*2^(count+1)=value.toNat*2:=by
      rw [Nat.pow_succ,←Nat.mul_assoc,←conserved]
    have addRead : eval source (addition 1)=some (.val (.word (BitVec.ofNat 64 (count+1)))):=by
      simp [eval,addition,localVar,evalHOLExact,evalListHOLExact,toExact,s,valueIsWord,valueWord,wordOpHOL,wordOp,←BitVec.ofNat_add]
    let added:=bind source "s" (BitVec.ofNat 64 (count+1))
    have addRun:=WitnessRadix.StateSteps.assign_execute source "s" (addition 1) _ _ s addRead
    have firstRun : evaluateHOLFiniteState source (.ite (test 1) (.assign .local (ofString "s") (addition 1)) .skip)=(none,added):=by
      rw [evaluateHOLFiniteState_ite,testRead]
      simpa only [if_pos take,if_neg (show (1#64 : BitVec 64)≠0 by decide)] using addRun
    have sAdded : added.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 (count+1)))):=bind_lookup_same _ _ _
    have returnRun : evaluateHOLFiniteState added (.return (localVar "s"))=
        (some (.returned (.val (.word (BitVec.ofNat 64 (count+1))))),emptyLocalsHOLFinite added):=by
      simp [evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,sAdded,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    refine ⟨count+1,by omega,?_,?_,?_⟩
    · rw [productEq]
      omega
    · rw [productEq]
      omega
    · rw [finish,WitnessRadix.StateSteps.next_sequence source added _ _ firstRun (Nat.le_refl _)]
      exact returnRun
  · have low : 2^31≤value.toNat:=by
      have bad : ¬value.toNat<2^(32-1):=fun small=>take ((mask_zero value 1 (by omega) valueSmall).mpr small)
      omega
    have firstRun : evaluateHOLFiniteState source (.ite (test 1) (.assign .local (ofString "s") (addition 1)) .skip)=(none,source):=by
      rw [evaluateHOLFiniteState_ite,testRead]
      simp [take]
    refine ⟨count,by omega,by omega,by omega,?_⟩
    rw [finish,WitnessRadix.StateSteps.next_sequence source source _ _ firstRun (Nat.le_refl _)]
    simp [evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,s,shapeOfHOLExact,sizeOfShapeWithContextHOL]

end InitECandidate.Solver.Input.UDivMod.Nlz32

#print axioms InitECandidate.Solver.Input.UDivMod.Nlz32.finish_execute


namespace InitECandidate.Solver.Input.UDivMod.Nlz32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

private theorem frame_clock_le (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame : target={source with locals:=target.locals}) : target.clock≤source.clock := by
  have clock:=congrArg PanSemStateFiniteExact.clock frame
  change target.clock=source.clock at clock
  omega

private theorem local_frames (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first : middle={source with locals:=middle.locals}) (second : target={middle with locals:=target.locals}) :
    target={source with locals:=target.locals} := by
  rw [second,first]

/-- Complete original leading-zero count on its real positive32-bit input.
The returned count normalizes that original word into [2^31,2^32). -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (valueSmall : value.toNat<2^32) (positive : 0<value.toNat)
    (x : source.locals.lookup (ofString "x")=some (.val (.word value))) :
    ∃ target bits,bits≤31 ∧ 2^31≤value.toNat*2^bits ∧ value.toNat*2^bits<2^32 ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 bits)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite source := by
  classical
  let entry:=bind source "s" 0#64
  have s0 : entry.locals.lookup (ofString "s")=some (.val (.word (BitVec.ofNat 64 0))):=bind_lookup_same _ _ _
  have x0 : entry.locals.lookup (ofString "x")=some (.val (.word value)):=
    (bind_lookup_other source "s" "x" 0#64 (by decide)).trans x
  obtain ⟨s16,v16,c16,c16Bound,lo16,hi16,e16,r16,f16,x16,n16⟩:=
    stage_execute entry value value 0 16 (by decide) valueSmall (by change 1≤value.toNat;omega) (by simp) x0 s0
  obtain ⟨s8,v8,c8,c8Bound,lo8,hi8,e8,r8,f8,x8,n8⟩:=
    stage_execute s16 value v16 c16 8 (by decide) hi16 lo16 e16 x16 n16
  obtain ⟨s4,v4,c4,c4Bound,lo4,hi4,e4,r4,f4,x4,n4⟩:=
    stage_execute s8 value v8 c8 4 (by decide) hi8 lo8 e8 x8 n8
  obtain ⟨s2,v2,c2,c2Bound,lo2,hi2,e2,r2,f2,x2,n2⟩:=
    stage_execute s4 value v4 c4 2 (by decide) hi4 lo4 e4 x4 n4
  obtain ⟨bits,bound,lower,upper,finishRun⟩:=finish_execute s2 value v2 c2 (by omega) hi2 lo2 e2 x2 n2
  have sequenceRun : evaluateHOLFiniteState entry (stages [16,8,4,2])=
      (some (.returned (.val (.word (BitVec.ofNat 64 bits)))),emptyLocalsHOLFinite s2):=by
    simp only [stages]
    rw [WitnessRadix.StateSteps.next_sequence entry s16 _ _ r16 (frame_clock_le _ _ f16),
      WitnessRadix.StateSteps.next_sequence s16 s8 _ _ r8 (frame_clock_le _ _ f8),
      WitnessRadix.StateSteps.next_sequence s8 s4 _ _ r4 (frame_clock_le _ _ f4),
      WitnessRadix.StateSteps.next_sequence s4 s2 _ _ r2 (frame_clock_le _ _ f2)]
    exact finishRun
  have declared:=ScalarScope.declare_execute source _ "s" (.const 0#64) 0#64 (stages [16,8,4,2]) _ rfl sequenceRun
  have frame8:=local_frames entry s16 s8 f16 f8
  have frame4:=local_frames entry s8 s4 frame8 f4
  have frame2:=local_frames entry s4 s2 frame4 f2
  let target:=restore source "s" (emptyLocalsHOLFinite s2)
  refine ⟨target,bits,bound,lower,upper,?_,?_⟩
  · rw [body_shape]
    exact declared
  · have frame:=congrArg emptyLocalsHOLFinite frame2
    change emptyLocalsHOLFinite s2=emptyLocalsHOLFinite source at frame ⊢
    exact frame

private theorem stage_cost (code) (amount : Nat) : ClockCost.Bound code (stage amount) 0 := by
  unfold stage active
  exact ClockCost.conditional code _ _ _ 0 0
    (ClockCost.sequence code _ _ 0 0 (ClockCost.assign code _ _) (ClockCost.assign code _ _)) (ClockCost.skip code)

private theorem finish_cost (code) : ClockCost.Bound code finish 0 := by
  unfold finish
  exact ClockCost.sequence code _ _ 0 0
    (ClockCost.conditional code _ _ _ 0 0 (ClockCost.assign code _ _) (ClockCost.skip code)) (ClockCost.returned code _)

private theorem stages_cost (code) (amounts : List Nat) : ClockCost.Bound code (stages amounts) 0 := by
  induction amounts with
  | nil=>exact finish_cost code
  | cons amount rest ih=>exact ClockCost.sequence code _ _ 0 0 (stage_cost code amount) ih

/-- All outcomes spend0body source ticks; target straight-line work is separate. -/
theorem body_cost (code) : ClockCost.Bound code body 0 := by
  rw [body_shape]
  exact ClockCost.declared code _ _ _ _ 0 (stages_cost code _)

theorem call_cost (code) (installed : OriginalCode.Installed code)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (tailBound : ClockCost.Bound code continuation tailPrice) :
    ClockCost.Bound code (.decCall (ofString name) .one (ofString "nlz32") arguments continuation) (tailPrice+1) := by
  simpa only [Nat.zero_add] using ClockCost.scoped_body code (ofString name) .one (ofString "nlz32") arguments continuation
    formals body .one 0 tailPrice (original_code code installed) (body_cost code) tailBound

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (installed : OriginalCode.Installed source.code)
    (valueSmall : value.toNat<2^32) (positive : 0<value.toNat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word value)])
    (enough : 1≤source.clock) :
    ∃ bits,bits≤31 ∧ 2^31≤value.toNat*2^bits ∧ value.toNat*2^bits<2^32 ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "nlz32") arguments continuation)=
        (let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1} name (BitVec.ofNat 64 bits)) continuation
        (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,x⟩:=CallNormal.unary_environment source.code.lookup (ofString "nlz32") "x" body value (original_code source.code installed)
  obtain ⟨target,bits,bound,lower,upper,run,frame⟩:=execute (callEntryStateHOLFinite source callee) value valueSmall positive x
  have actual:=CallNormal.pure_return_execute source target name (ofString "nlz32") arguments _ body continuation callee
    (BitVec.ofNat 64 bits) 0 args called enough run frame
  exact ⟨bits,bound,lower,upper,by simpa only [Nat.sub_zero] using actual⟩

end InitECandidate.Solver.Input.UDivMod.Nlz32

#print axioms InitECandidate.Solver.Input.UDivMod.Nlz32.execute
#print axioms InitECandidate.Solver.Input.UDivMod.Nlz32.body_cost
#print axioms InitECandidate.Solver.Input.UDivMod.Nlz32.call_cost
#print axioms InitECandidate.Solver.Input.UDivMod.Nlz32.call_execute


namespace InitECandidate.Solver.Input.UDivMod.Nlz32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual normalized top-digit expression includes a carry from the
previous digit. Its mask retains the normalized leading half-bit. -/
theorem normalized_digit (leading previous : BitVec 64) (bits : Nat) (bitsSmall : bits≤31)
    (lower : 2^31≤leading.toNat*2^bits) (upper : leading.toNat*2^bits<2^32) :
    2^31≤((((leading<<<bits) ||| (previous>>>(32-bits))) &&& 4294967295#64).toNat) ∧
      ((((leading<<<bits) ||| (previous>>>(32-bits))) &&& 4294967295#64).toNat)<2^32 := by
  have leftNumber : (leading<<<bits).toNat=leading.toNat*2^bits:=by
    rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.mod_eq_of_lt (by omega)]
  have leftMask : (leading<<<bits) &&& 4294967295#64=leading<<<bits:=by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    change (leading<<<bits).toNat &&& (2^32-1)=(leading<<<bits).toNat
    rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt (by omega)]
  have joined : ((leading<<<bits) ||| (previous>>>(32-bits))) &&& 4294967295#64=
      (leading<<<bits) ||| ((previous>>>(32-bits)) &&& 4294967295#64):=by
    rw [BitVec.and_or_distrib_right,leftMask]
  constructor
  · rw [joined,BitVec.toNat_or]
    have grows : (leading<<<bits).toNat≤(leading<<<bits).toNat ||| ((previous>>>(32-bits)) &&& 4294967295#64).toNat:=Nat.left_le_or
    omega
  · rw [BitVec.toNat_and]
    change ((leading<<<bits) ||| (previous>>>(32-bits))).toNat &&& (2^32-1)<2^32
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)

/-- The genuine current unary ABI exposes the actual normalization count
and resumes its caller with exactly the one-call decrement. -/
theorem resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (value : BitVec 64)
    (installed : OriginalCode.Installed source.code) (valueSmall : value.toNat<2^32) (positive : 0<value.toNat)
    (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "nlz32") [.val (.word value)]=some (actual,callee,shape))
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual=(some (.returned returned),target)) :
    ∃ bits,bits≤31 ∧ 2^31≤value.toNat*2^bits ∧ value.toNat*2^bits<2^32 ∧ returned=.val (.word (BitVec.ofNat 64 bits)) ∧
      CallNormal.continuationEntry source target name returned=bind {source with clock:=source.clock-1} name (BitVec.ofNat 64 bits) := by
  obtain ⟨expected,lookup,xCell⟩:=CallNormal.unary_environment source.code.lookup (ofString "nlz32") "x" body value (original_code source.code installed)
  have same:=Option.some.inj (called.symm.trans lookup)
  have bodyEq : actual=body:=congrArg Prod.fst same
  have calleeEq : callee=expected:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  rw [←calleeEq] at xCell
  rw [bodyEq] at run
  obtain ⟨post,bits,bound,lower,upper,completed,frame⟩:=execute (callEntryStateHOLFinite source callee) value valueSmall positive xCell
  have actualEq:=run.symm.trans completed
  have result : returned=.val (.word (BitVec.ofNat 64 bits)):=by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using congrArg Prod.fst actualEq
  have targetEq : target=post:=congrArg Prod.snd actualEq
  rw [←targetEq] at frame
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  change {target with locals:=source.locals}={source with clock:=source.clock-1} at callerFrame
  refine ⟨bits,bound,lower,upper,result,?_⟩
  change setVarHOLFinite (ofString name) returned {target with locals:=source.locals}=
    setVarHOLFinite (ofString name) (.val (.word (BitVec.ofNat 64 bits))) {source with clock:=source.clock-1}
  rw [result,callerFrame]

end InitECandidate.Solver.Input.UDivMod.Nlz32

#print axioms InitECandidate.Solver.Input.UDivMod.Nlz32.normalized_digit
#print axioms InitECandidate.Solver.Input.UDivMod.Nlz32.resume


namespace InitECandidate.Solver.Input.UDivMod.QhatCorrection
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def test : ExpHOL 64:=.cmp .equal (localVar "again") (.const 1#64)
def roomTest : ExpHOL 64:=.cmp .lower (localVar "rhat") (.const 4294967296#64)
def leftEstimate : ExpHOL 64:=.op .or [.shift .lsl (localVar "rhat") (.const 32#64),localVar "ujn2"]
def rightEstimate : ExpHOL 64:=.panop .mul [localVar "qhat",localVar "vsec"]
def estimateTest : ExpHOL 64:=.cmp .lower leftEstimate rightEstimate
def quotientExpression : ExpHOL 64:=.op .sub [localVar "qhat",.const 1#64]
def remainderExpression : ExpHOL 64:=.op .add [localVar "rhat",localVar "vtop"]
def correct : ProgHOL 64:=.seq (.assign .local (ofString "qhat") quotientExpression)
  (.seq (.assign .local (ofString "rhat") remainderExpression) (.assign .local (ofString "again") (.const 1#64)))
def branch : ProgHOL 64:=.ite roomTest (.ite estimateTest correct .skip) .skip
def body : ProgHOL 64:=.seq (.assign .local (ofString "again") (.const 0#64)) branch
def loop : ProgHOL 64:=.while test body

def divmnuBody : ProgHOL 64:=match Guest.Software.guestFn_divmnu with | .function fn=>progToHOL fn.body | _=>.skip
private def findLoop : ProgHOL 64→Option (ProgHOL 64)
  | .while condition body=>
    match condition with
    | .cmp .equal (.var .local name) (.const word)=>
      if name=ofString "again" ∧ word=1#64 then some (.while condition body) else findLoop body
    | _=>findLoop body
  | .seq first rest=>(findLoop first).orElse (fun _=>findLoop rest)
  | .ite _ first rest=>(findLoop first).orElse (fun _=>findLoop rest)
  | .dec _ _ _ rest=>findLoop rest
  | .decCall _ _ _ _ rest=>findLoop rest
  | _=>none

set_option maxRecDepth 100000 in
/-- Syntactic extraction of the literal original divmnu correction loop. -/
theorem literal_loop : findLoop divmnuBody=some loop := by
  simp [findLoop,divmnuBody,Guest.Software.guestFn_divmnu,progToHOL,expToHOL,shapeToHOL,
    loop,test,body,branch,roomTest,estimateTest,leftEstimate,rightEstimate,correct,quotientExpression,remainderExpression,localVar]

structure Bindings (source : PanSemStateFiniteExact 64 Guest.HostMemory) (q r flag top second low : BitVec 64) : Prop where
  qCell : source.locals.lookup (ofString "qhat")=some (.val (.word q))
  rCell : source.locals.lookup (ofString "rhat")=some (.val (.word r))
  flagCell : source.locals.lookup (ofString "again")=some (.val (.word flag))
  topCell : source.locals.lookup (ofString "vtop")=some (.val (.word top))
  secondCell : source.locals.lookup (ofString "vsec")=some (.val (.word second))
  lowCell : source.locals.lookup (ofString "ujn2")=some (.val (.word low))

private theorem Bindings.set_again {source : PanSemStateFiniteExact 64 Guest.HostMemory} {q r flag top second low : BitVec 64}
    (ready : Bindings source q r flag top second low) (next : BitVec 64) :
    Bindings (bind source "again" next) q r next top second low := by
  exact ⟨(bind_lookup_other source "again" "qhat" next (by decide)).trans ready.qCell,
    (bind_lookup_other source "again" "rhat" next (by decide)).trans ready.rCell,bind_lookup_same _ _ _,
    (bind_lookup_other source "again" "vtop" next (by decide)).trans ready.topCell,
    (bind_lookup_other source "again" "vsec" next (by decide)).trans ready.secondCell,
    (bind_lookup_other source "again" "ujn2" next (by decide)).trans ready.lowCell⟩

private theorem Bindings.set_qhat {source : PanSemStateFiniteExact 64 Guest.HostMemory} {q r flag top second low : BitVec 64}
    (ready : Bindings source q r flag top second low) (next : BitVec 64) :
    Bindings (bind source "qhat" next) next r flag top second low := by
  exact ⟨bind_lookup_same _ _ _,(bind_lookup_other source "qhat" "rhat" next (by decide)).trans ready.rCell,
    (bind_lookup_other source "qhat" "again" next (by decide)).trans ready.flagCell,
    (bind_lookup_other source "qhat" "vtop" next (by decide)).trans ready.topCell,
    (bind_lookup_other source "qhat" "vsec" next (by decide)).trans ready.secondCell,
    (bind_lookup_other source "qhat" "ujn2" next (by decide)).trans ready.lowCell⟩

private theorem Bindings.set_rhat {source : PanSemStateFiniteExact 64 Guest.HostMemory} {q r flag top second low : BitVec 64}
    (ready : Bindings source q r flag top second low) (next : BitVec 64) :
    Bindings (bind source "rhat" next) q next flag top second low := by
  exact ⟨(bind_lookup_other source "rhat" "qhat" next (by decide)).trans ready.qCell,bind_lookup_same _ _ _,
    (bind_lookup_other source "rhat" "again" next (by decide)).trans ready.flagCell,
    (bind_lookup_other source "rhat" "vtop" next (by decide)).trans ready.topCell,
    (bind_lookup_other source "rhat" "vsec" next (by decide)).trans ready.secondCell,
    (bind_lookup_other source "rhat" "ujn2" next (by decide)).trans ready.lowCell⟩

def corrects (q r second low : BitVec 64) : Prop:=
  r.toNat<4294967296 ∧ ((r<<<(32:Nat)) ||| low).toNat<(q*second).toNat
instance (q r second low : BitVec 64) : Decidable (corrects q r second low):=inferInstanceAs (Decidable (_∧_))
def nextQ (q r second low : BitVec 64) : BitVec 64:=if corrects q r second low then q-1#64 else q
def nextR (q r top second low : BitVec 64) : BitVec 64:=if corrects q r second low then r+top else r
def nextFlag (q r second low : BitVec 64) : BitVec 64:=if corrects q r second low then 1#64 else 0#64
def step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (q r top second low : BitVec 64) :=
  let cleared:=bind source "again" 0#64
  if corrects q r second low then bind (bind (bind cleared "qhat" (q-1#64)) "rhat" (r+top)) "again" 1#64 else cleared

theorem step_bindings (source : PanSemStateFiniteExact 64 Guest.HostMemory) (q r flag top second low : BitVec 64)
    (ready : Bindings source q r flag top second low) :
    Bindings (step source q r top second low) (nextQ q r second low) (nextR q r top second low) (nextFlag q r second low) top second low := by
  by_cases take : corrects q r second low
  · simp only [step,nextQ,nextR,nextFlag,if_pos take]
    exact (((ready.set_again 0#64).set_qhat (q-1#64)).set_rhat (r+top)).set_again 1#64
  · simp only [step,nextQ,nextR,nextFlag,if_neg take]
    exact ready.set_again 0#64

theorem body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (q r flag top second low : BitVec 64)
    (ready : Bindings source q r flag top second low) :
    evaluateHOLFiniteState source body=(none,step source q r top second low) := by
  classical
  let cleared:=bind source "again" 0#64
  have clearReady : Bindings cleared q r 0#64 top second low:=ready.set_again 0#64
  have clearRun:=WitnessRadix.StateSteps.assign_execute source "again" (.const 0#64) flag 0#64 ready.flagCell rfl
  have roomRead : eval cleared roomTest=some (.val (.word (if r.toNat<4294967296 then 1#64 else 0#64))):=by
    simp [eval,roomTest,localVar,evalHOLExact,toExact,clearReady.rCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  have estimateRead : eval cleared estimateTest=some (.val (.word (if ((r<<<(32:Nat)) ||| low).toNat<(q*second).toNat then 1#64 else 0#64))):=by
    simp [eval,estimateTest,leftEstimate,rightEstimate,localVar,evalHOLExact,evalListHOLExact,toExact,
      clearReady.rCell,clearReady.qCell,clearReady.secondCell,clearReady.lowCell,valueWord,valueIsWord,wordOpHOL,wordOp,
      wordShiftHOL,panOpHOL,OrOp.or,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  simp only [eval] at roomRead estimateRead
  rw [body,WitnessRadix.StateSteps.next_sequence source cleared _ _ clearRun (Nat.le_refl _)]
  rw [branch,evaluateHOLFiniteState_ite,roomRead]
  by_cases room : r.toNat<4294967296
  · rw [if_pos room]
    simp only [if_neg (show (1#64 : BitVec 64)≠0 by decide)]
    rw [evaluateHOLFiniteState_ite,estimateRead]
    by_cases take : ((r<<<(32:Nat)) ||| low).toNat<(q*second).toNat
    · rw [if_pos take]
      simp only [if_neg (show (1#64 : BitVec 64)≠0 by decide)]
      have qRead : eval cleared quotientExpression=some (.val (.word (q-1#64))):=by
        simp [eval,quotientExpression,evalHOLExact,evalListHOLExact,toExact,localVar,clearReady.qCell,valueWord,valueIsWord,wordOpHOL,wordOp]
      have qRun:=WitnessRadix.StateSteps.assign_execute cleared "qhat" quotientExpression q (q-1#64) clearReady.qCell qRead
      let qPost:=bind cleared "qhat" (q-1#64)
      have qReady : Bindings qPost (q-1#64) r 0#64 top second low:=clearReady.set_qhat (q-1#64)
      have rRead : eval qPost remainderExpression=some (.val (.word (r+top))):=by
        simp [eval,remainderExpression,evalHOLExact,evalListHOLExact,toExact,localVar,qReady.rCell,qReady.topCell,valueWord,valueIsWord,wordOpHOL,wordOp]
      have rRun:=WitnessRadix.StateSteps.assign_execute qPost "rhat" remainderExpression r (r+top) qReady.rCell rRead
      let rPost:=bind qPost "rhat" (r+top)
      have rReady : Bindings rPost (q-1#64) (r+top) 0#64 top second low:=qReady.set_rhat (r+top)
      have againRun:=WitnessRadix.StateSteps.assign_execute rPost "again" (.const 1#64) 0#64 1#64 rReady.flagCell rfl
      rw [correct,WitnessRadix.StateSteps.next_sequence cleared qPost _ _ qRun (Nat.le_refl _),
        WitnessRadix.StateSteps.next_sequence qPost rPost _ _ rRun (Nat.le_refl _)]
      have active : corrects q r second low:=⟨room,take⟩
      simpa only [step,if_pos active] using againRun
    · rw [if_neg take]
      have inactive : ¬corrects q r second low:=fun active=>take active.2
      simp only [if_pos (show (0#64 : BitVec 64)=0 from rfl),evaluateHOLFiniteState_skip,step,if_neg inactive]
      rfl
  · rw [if_neg room]
    have inactive : ¬corrects q r second low:=fun active=>room active.1
    simp only [if_pos (show (0#64 : BitVec 64)=0 from rfl),evaluateHOLFiniteState_skip,step,if_neg inactive]
    rfl

end InitECandidate.Solver.Input.UDivMod.QhatCorrection

#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.literal_loop
#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.step_bindings
#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.body_execute


namespace InitECandidate.Solver.Input.UDivMod.QhatCorrection
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def stageRank (r flag : BitVec 64) : Nat:=
  if flag=1#64 then if r.toNat<2147483648 then 3 else if r.toNat<4294967296 then 2 else 1 else 0
private def readWord (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) : BitVec 64:=
  valueWord ((source.locals.lookup (ofString name)).getD (.val (.word 0#64)))
def rank (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat:=stageRank (readWord source "rhat") (readWord source "again")

theorem stage_rank_bound (r flag : BitVec 64) : stageRank r flag≤3 := by
  unfold stageRank
  split_ifs <;> omega

private theorem stage_rank_positive (r : BitVec 64) : 0<stageRank r 1#64 := by
  simp only [stageRank,if_pos rfl]
  split_ifs <;> omega

private theorem rank_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (q r flag top second low : BitVec 64)
    (ready : Bindings source q r flag top second low) : rank source=stageRank r flag := by
  simp only [rank,readWord,ready.rCell,ready.flagCell,Option.getD_some,valueWord]

/-- Each continuing correction increases the remainder estimate by at least
half a digit; every other outcome clears the real again flag. -/
theorem stage_rank_step (q r top second low : BitVec 64)
    (topLarge : 2147483648≤top.toNat) (topSmall : top.toNat<4294967296) :
    stageRank (nextR q r top second low) (nextFlag q r second low)<stageRank r 1#64 := by
  by_cases active : corrects q r second low
  · have room : r.toNat<4294967296:=active.1
    have increment : (r+top).toNat=r.toNat+top.toNat:=by
      rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by omega)]
    simp only [nextR,nextFlag,if_pos active,stageRank,if_pos rfl,increment]
    split_ifs <;> omega
  · have positive:=stage_rank_positive r
    simpa only [nextFlag,if_neg active,stageRank,if_neg (show (0#64 : BitVec 64)≠1#64 by decide),if_pos rfl] using positive

theorem body_cost (code) : ClockCost.Bound code body 0 := by
  unfold body branch correct
  exact ClockCost.sequence code _ _ 0 0 (ClockCost.assign code _ _)
    (ClockCost.conditional code _ _ _ 0 0
      (ClockCost.conditional code _ _ _ 0 0
        (ClockCost.sequence code _ _ 0 0 (ClockCost.assign code _ _)
          (ClockCost.sequence code _ _ 0 0 (ClockCost.assign code _ _) (ClockCost.assign code _ _)))
        (ClockCost.skip code)) (ClockCost.skip code))

private theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (flag : BitVec 64)
    (cell : source.locals.lookup (ofString "again")=some (.val (.word flag))) :
    evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) test=
      some (.val (.word (if flag=1#64 then 1#64 else 0#64))) := by
  rw [finite_eval]
  simp [eval,test,evalHOLExact,toExact,localVar,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- All actual outcomes of the literal current correction loop cost≤3
source ticks, including clock exhaustion. No completed trace is assumed. -/
theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (q r flag top second low : BitVec 64)
    (ready : Bindings source q r flag top second low)
    (topLarge : 2147483648≤top.toNat) (topSmall : top.toNat<4294967296) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤3 := by
  classical
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ q r flag,Bindings current q r flag top second low
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      current.code=source.code→invariant current→∀ observed : BitVec 64,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word observed))→
      observed≠0→0<rank current ∧ (current.clock≠0→
        let output:=evaluateHOLFiniteState (decClockHOLFinite current) body
        (output.1=none ∨ output.1=some .continue)→invariant output.2 ∧ rank output.2<rank current) := by
    intro current installed valid observed actual nonzero
    obtain ⟨q,r,flag,currentReady⟩:=valid
    have expected:=test_read current flag currentReady.flagCell
    have active : flag=1#64:=by
      by_contra inactive
      rw [if_neg inactive] at expected
      have zero : observed=0#64:=by
        simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actual.symm.trans expected
      exact nonzero zero
    subst flag
    have oldRank:=rank_read current q r 1#64 top second low currentReady
    refine ⟨by rw [oldRank];exact stage_rank_positive r,?_⟩
    intro funded
    have entryReady : Bindings (decClockHOLFinite current) q r 1#64 top second low:=
      ⟨currentReady.qCell,currentReady.rCell,currentReady.flagCell,currentReady.topCell,currentReady.secondCell,currentReady.lowCell⟩
    have run:=body_execute (decClockHOLFinite current) q r 1#64 top second low entryReady
    dsimp only
    intro continuing
    rw [run]
    have nextReady:=step_bindings (decClockHOLFinite current) q r 1#64 top second low entryReady
    refine ⟨⟨nextQ q r second low,nextR q r top second low,nextFlag q r second low,nextReady⟩,?_⟩
    rw [rank_read _ _ _ _ _ _ _ nextReady,oldRank]
    exact stage_rank_step q r top second low topLarge topSmall
  have bounded:=ClockCost.ranked_loop source.code test body 0 invariant rank (body_cost source.code) progress source rfl ⟨q,r,flag,ready⟩
  have small : rank source≤3:=by rw [rank_read _ _ _ _ _ _ _ ready];exact stage_rank_bound r flag
  change source.clock-(evaluateHOLFiniteState source loop).2.clock≤(0+1)*rank source at bounded
  omega

end InitECandidate.Solver.Input.UDivMod.QhatCorrection

#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.stage_rank_bound
#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.stage_rank_step
#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.body_cost
#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.loop_cost


namespace InitECandidate.Solver.Input.UDivMod.QhatCorrection
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem body_safe : LocalPrefix (ofString "vtop") body := by
  unfold body branch correct
  exact .seq (.assign _ _ (by decide)) (.ite _
    (.ite _ (.seq (.assign _ _ (by decide)) (.seq (.assign _ _ (by decide)) (.assign _ _ (by decide)))) .skip) .skip)

theorem loop_frame (code) : LocalEffects.Preserves code loop := by
  unfold loop body branch correct
  exact LocalEffects.loop code _ _
    (LocalEffects.sequence code _ _ (LocalEffects.assign code _ _)
      (LocalEffects.conditional code _ _ _
        (LocalEffects.conditional code _ _ _
          (LocalEffects.sequence code _ _ (LocalEffects.assign code _ _)
            (LocalEffects.sequence code _ _ (LocalEffects.assign code _ _) (LocalEffects.assign code _ _)))
          (LocalEffects.skip code)) (LocalEffects.skip code)))

/-- The actual unsigned comparison cannot correct a zero quotient, so its
subtraction never wraps, regardless of the second divisor digit. -/
theorem correction_positive (q r second low : BitVec 64) (active : corrects q r second low) : 0<q.toNat := by
  by_contra bad
  have zero : q=0#64:=BitVec.eq_of_toNat_eq (by change q.toNat=0;omega)
  have impossible:=active.2
  simp only [zero,BitVec.zero_mul,BitVec.toNat_zero,Nat.not_lt_zero] at impossible

/-- Exact natural effect of a real correction, including the guard that
prevents quotient wrap and the32-bit room that prevents remainder wrap. -/
theorem step_arithmetic (q r top second low : BitVec 64) (topSmall : top.toNat<4294967296) :
    (nextQ q r second low).toNat+(if corrects q r second low then 1 else 0)=q.toNat ∧
      (nextR q r top second low).toNat=r.toNat+(if corrects q r second low then 1 else 0)*top.toNat := by
  by_cases active : corrects q r second low
  · have positive:=correction_positive q r second low active
    have room:=active.1
    have oneBelow : (1#64 : BitVec 64)≤q:=by change 1≤q.toNat;omega
    have quotient : (q-1#64).toNat+1=q.toNat:=by
      rw [BitVec.toNat_sub_of_le oneBelow]
      change q.toNat-1+1=q.toNat
      omega
    have remainder : (r+top).toNat=r.toNat+top.toNat:=by
      rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by omega)]
    simpa only [nextQ,nextR,if_pos active,Nat.one_mul] using And.intro quotient remainder
  · simp [nextQ,nextR,active]

end InitECandidate.Solver.Input.UDivMod.QhatCorrection

#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.body_safe
#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.loop_frame
#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.correction_positive
#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.step_arithmetic


namespace InitECandidate.Solver.Input.UDivMod.QhatCorrection
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

private theorem step_rank_budget (q r top second low : BitVec 64)
    (topLarge : 2147483648≤top.toNat) (topSmall : top.toNat<4294967296) :
    (if corrects q r second low then 1 else 0)+stageRank (nextR q r top second low) 1#64≤stageRank r 1#64 := by
  by_cases active : corrects q r second low
  · have smaller:=stage_rank_step q r top second low topLarge topSmall
    simp only [nextFlag,if_pos active] at smaller ⊢
    omega
  · simp only [nextR,if_neg active,Nat.zero_add]
    omega

/-- Finite sequence of the actual enabled quotient corrections. -/
inductive Trace (top second low : BitVec 64) : BitVec 64→BitVec 64→BitVec 64→BitVec 64→Nat→Prop where
  | refl (q r : BitVec 64) : Trace top second low q r q r 0
  | snoc {q0 r0 q r : BitVec 64} {count : Nat}
      (previous : Trace top second low q0 r0 q r count) (active : corrects q r second low) :
      Trace top second low q0 r0 (q-1#64) (r+top) (count+1)

theorem Trace.preserves {top second low q0 r0 finalQ finalR : BitVec 64} {count : Nat}
    (route : Trace top second low q0 r0 finalQ finalR count) (property : BitVec 64→BitVec 64→Prop)
    (initial : property q0 r0)
    (advance : ∀ q r,property q r→corrects q r second low→property (q-1#64) (r+top)) : property finalQ finalR := by
  induction route with
  | refl=>exact initial
  | snoc previous active ih=>exact advance _ _ ih active

/-- An actual normal exit has made at most two genuine corrections. The
returned local estimates retain exact natural subtraction/addition history,
stop at the literal guard, and preserve every nonlocal field. -/
theorem loop_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (q r top second low : BitVec 64)
    (ready : Bindings source q r 1#64 top second low)
    (topLarge : 2147483648≤top.toNat) (topSmall : top.toNat<4294967296)
    (normal : evaluateHOLFiniteState source loop=(none,post)) :
    ∃ finalQ finalR corrections,corrections≤2 ∧ Bindings post finalQ finalR 0#64 top second low ∧
      finalQ.toNat+corrections=q.toNat ∧ finalR.toNat=r.toNat+corrections*top.toNat ∧
      ¬corrects finalQ finalR second low ∧ Trace top second low q r finalQ finalR corrections ∧
      LocalEffects.erase post=LocalEffects.erase source := by
  classical
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>
    ∃ currentQ currentR flag corrections,Bindings current currentQ currentR flag top second low ∧
      (flag=1#64 ∨ (flag=0#64 ∧ ¬corrects currentQ currentR second low)) ∧
      currentQ.toNat+corrections=q.toNat ∧ currentR.toNat=r.toNat+corrections*top.toNat ∧
      corrections+stageRank currentR 1#64≤stageRank r 1#64 ∧ Trace top second low q r currentQ currentR corrections
  have initial : invariant source:=by
    exact ⟨q,r,1#64,0,ready,Or.inl rfl,by simp,by simp,by simp,Trace.refl q r⟩
  have transition : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→
      ∀ observed : BitVec 64,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word observed))→
      observed≠0→current.clock≠0→∀ target,evaluateHOLFiniteState (decClockHOLFinite current) body=(none,target)→invariant target := by
    intro current installed valid observed actual nonzero funded target run
    obtain ⟨currentQ,currentR,flag,corrections,currentReady,flagFact,quotientOld,remainderOld,budgetOld,route⟩:=valid
    have expected:=test_read current flag currentReady.flagCell
    have activeFlag : flag=1#64:=by
      by_contra inactive
      rw [if_neg inactive] at expected
      have zero : observed=0#64:=by
        simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actual.symm.trans expected
      exact nonzero zero
    subst flag
    have entryReady : Bindings (decClockHOLFinite current) currentQ currentR 1#64 top second low:=
      ⟨currentReady.qCell,currentReady.rCell,currentReady.flagCell,currentReady.topCell,currentReady.secondCell,currentReady.lowCell⟩
    have expectedRun:=body_execute (decClockHOLFinite current) currentQ currentR 1#64 top second low entryReady
    have targetEq : target=step (decClockHOLFinite current) currentQ currentR top second low:=congrArg Prod.snd (run.symm.trans expectedRun)
    rw [targetEq]
    have nextReady:=step_bindings (decClockHOLFinite current) currentQ currentR 1#64 top second low entryReady
    let added : Nat:=if corrects currentQ currentR second low then 1 else 0
    obtain ⟨quotientStep,remainderStep⟩:=step_arithmetic currentQ currentR top second low topSmall
    have quotientNumber : (nextQ currentQ currentR second low).toNat+added=currentQ.toNat:=quotientStep
    have remainderNumber : (nextR currentQ currentR top second low).toNat=currentR.toNat+added*top.toNat:=remainderStep
    have budgetStep : added+stageRank (nextR currentQ currentR top second low) 1#64≤stageRank currentR 1#64:=
      step_rank_budget currentQ currentR top second low topLarge topSmall
    refine ⟨nextQ currentQ currentR second low,nextR currentQ currentR top second low,nextFlag currentQ currentR second low,
      corrections+added,nextReady,?_,?_,?_,?_,?_⟩
    · by_cases active : corrects currentQ currentR second low
      · exact Or.inl (by simp only [nextFlag,if_pos active])
      · exact Or.inr ⟨by simp only [nextFlag,if_neg active],by simpa only [nextQ,nextR,if_neg active] using active⟩
    · omega
    · rw [remainderNumber,remainderOld,Nat.add_mul]
      omega
    · omega
    · by_cases active : corrects currentQ currentR second low
      · simpa only [nextQ,nextR,if_pos active,added] using Trace.snoc route active
      · simpa only [nextQ,nextR,if_neg active,added,Nat.add_zero] using route
  have completed:=loop_invariant_summary source.code (ofString "vtop") test body (fun current=>body_safe.summary_full current)
    invariant transition source post rfl initial normal
  obtain ⟨finalQ,finalR,flag,corrections,postReady,flagFact,quotient,remainder,budget,route⟩:=completed
  have noBreak : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,(evaluateHOLFiniteState current body).1≠some .break:=by
    intro current
    have summary:=body_safe.summary_full current
    unfold LocalSummary at summary
    exact summary.2.2.1
  have exit:=loop_normal_exit test body noBreak source post normal
  have expectedExit:=test_read post flag postReady.flagCell
  have inactive : flag≠1#64:=by
    intro active
    rw [if_pos active] at expectedExit
    have impossible : (0#64 : BitVec 64)=1#64:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using exit.symm.trans expectedExit
    exact (by decide : (0#64 : BitVec 64)≠1#64) impossible
  obtain ⟨zero,stopped⟩ : flag=0#64 ∧ ¬corrects finalQ finalR second low:=by
    rcases flagFact with active|stopped
    · exact (inactive active).elim
    · exact stopped
  rw [zero] at postReady
  have bound : corrections≤2:=by
    have upper:=stage_rank_bound r 1#64
    have positive:=stage_rank_positive finalR
    omega
  have frame:=loop_frame source.code source rfl
  rw [normal] at frame
  exact ⟨finalQ,finalR,corrections,bound,postReady,quotient,remainder,stopped,route,frame⟩

end InitECandidate.Solver.Input.UDivMod.QhatCorrection

#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.loop_normal


namespace InitECandidate.Solver.Input.UDivMod.QhatCorrection
open Flapjack

/-- On genuine32-bit digits, the original wrapped-word comparison is exactly
the natural quotient-correction inequality, including the room guard. -/
theorem corrects_iff (q r second low : BitVec 64) (qSmall : q.toNat<4294967296)
    (secondSmall : second.toNat<4294967296) (lowSmall : low.toNat<4294967296) :
    corrects q r second low ↔ r.toNat*4294967296+low.toNat<q.toNat*second.toNat := by
  have productBound : q.toNat*second.toNat<2^64:=by
    calc _≤4294967295*4294967295:=Nat.mul_le_mul (by omega) (by omega)
         _<2^64:=by decide
  have productNumber : (q*second).toNat=q.toNat*second.toNat:=by
    rw [BitVec.toNat_mul,Nat.mod_eq_of_lt productBound]
  have leftNumber (room : r.toNat<4294967296) : ((r<<<(32:Nat)) ||| low).toNat=r.toNat*4294967296+low.toNat:=by
    have shifted : (r<<<(32:Nat)).toNat=r.toNat*4294967296:=by
      rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_or,shifted]
    have joined:=Nat.two_pow_add_eq_or_of_lt (i:=32) lowSmall r.toNat
    change r.toNat*2^32 ||| low.toNat=r.toNat*2^32+low.toNat
    rw [Nat.mul_comm r.toNat (2^32)]
    exact joined.symm
  constructor
  · intro active
    have compared:=active.2
    rw [leftNumber active.1,productNumber] at compared
    exact compared
  · intro compared
    have room : r.toNat<4294967296:=by omega
    exact ⟨room,by rw [leftNumber room,productNumber];exact compared⟩

end InitECandidate.Solver.Input.UDivMod.QhatCorrection

#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.Trace.preserves
#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.corrects_iff


namespace InitECandidate.Solver.Input.UDivMod.QhatCorrection
open Flapjack

/-- Starting from an upper quotient estimate, the actual enabled correction
history ends at the exact quotient for a two-digit divisor. -/
theorem Trace.quotient {top second low q0 r0 finalQ finalR : BitVec 64} {count : Nat}
    (route : Trace top second low q0 r0 finalQ finalR count)
    (topLarge : 2147483648≤top.toNat) (topSmall : top.toNat<4294967296)
    (qSmall : q0.toNat<4294967296) (secondSmall : second.toNat<4294967296) (lowSmall : low.toNat<4294967296)
    (initialUpper : ((q0.toNat*top.toNat+r0.toNat)*4294967296+low.toNat)/(top.toNat*4294967296+second.toNat)≤q0.toNat)
    (stopped : ¬corrects finalQ finalR second low) :
    finalQ.toNat=((q0.toNat*top.toNat+r0.toNat)*4294967296+low.toNat)/(top.toNat*4294967296+second.toNat) := by
  let upperPart:=q0.toNat*top.toNat+r0.toNat
  let divisor:=top.toNat*4294967296+second.toNat
  let total:=upperPart*4294967296+low.toNat
  have positive : 0<divisor:=by dsimp [divisor];omega
  let property:=fun q r : BitVec 64=>q.toNat<4294967296 ∧ q.toNat*top.toNat+r.toNat=upperPart ∧ total/divisor≤q.toNat
  have initial : property q0 r0:=⟨qSmall,rfl,initialUpper⟩
  have advance : ∀ q r : BitVec 64,property q r→corrects q r second low→property (q-1#64) (r+top) := by
    intro q r valid active
    obtain ⟨small,conserved,lower⟩:=valid
    obtain ⟨quotient,remainder⟩:=step_arithmetic q r top second low topSmall
    simp only [nextQ,nextR,if_pos active,Nat.one_mul] at quotient remainder
    have compared:=(corrects_iff q r second low small secondSmall lowSmall).mp active
    have below : total<q.toNat*divisor:=by
      dsimp [total,divisor]
      rw [←conserved]
      nlinarith [compared]
    have quotientBelow : total/divisor<q.toNat:=(Nat.div_lt_iff_lt_mul positive).mpr below
    refine ⟨by omega,?_,by omega⟩
    calc (q-1#64).toNat*top.toNat+(r+top).toNat=
          ((q-1#64).toNat+1)*top.toNat+r.toNat:=by rw [remainder];ring
      _=upperPart:=by rw [quotient,conserved]
  obtain ⟨finalSmall,conserved,lower⟩:=route.preserves property initial advance
  have compared : finalQ.toNat*second.toNat≤finalR.toNat*4294967296+low.toNat:=by
    by_contra bad
    exact stopped ((corrects_iff finalQ finalR second low finalSmall secondSmall lowSmall).mpr (by omega))
  have productBelow : finalQ.toNat*divisor≤total:=by
    dsimp [total,divisor]
    rw [←conserved]
    nlinarith [compared]
  have upper : finalQ.toNat≤total/divisor:=(Nat.le_div_iff_mul_le positive).mpr productBelow
  exact Nat.le_antisymm upper lower

/-- The ordinary div64by32 estimate is an upper estimate because its
returned remainder is below the top divisor digit. -/
theorem initial_upper (q r top second low : BitVec 64)
    (remainderSmall : r.toNat<top.toNat) (lowSmall : low.toNat<4294967296) :
    ((q.toNat*top.toNat+r.toNat)*4294967296+low.toNat)/(top.toNat*4294967296+second.toNat)≤q.toNat := by
  have positive : 0<top.toNat*4294967296+second.toNat:=by omega
  have below : (q.toNat*top.toNat+r.toNat)*4294967296+low.toNat<
      (q.toNat+1)*(top.toNat*4294967296+second.toNat):=by
    nlinarith [Nat.zero_le ((q.toNat+1)*second.toNat)]
  have upper:= (Nat.div_lt_iff_lt_mul positive).mpr below
  omega

end InitECandidate.Solver.Input.UDivMod.QhatCorrection

#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.Trace.quotient
#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.initial_upper


namespace InitECandidate.Solver.Input.UDivMod.QhatCorrection
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

private theorem join_number (high low : BitVec 64) (highSmall : high.toNat<4294967296) (lowSmall : low.toNat<4294967296) :
    ((high<<<(32:Nat)) ||| low).toNat=high.toNat*4294967296+low.toNat := by
  have shifted : (high<<<(32:Nat)).toNat=high.toNat*4294967296:=by
    rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_or,shifted]
  have joined:=Nat.two_pow_add_eq_or_of_lt (i:=32) lowSmall high.toNat
  change high.toNat*2^32 ||| low.toNat=high.toNat*2^32+low.toNat
  rw [Nat.mul_comm high.toNat (2^32)]
  exact joined.symm

/-- The original max-digit estimate branch conserves the high two input
digits and gives an upper quotient estimate whenever the quotient is a digit. -/
theorem max_initial_upper (high middle low top second : BitVec 64)
    (highSmall : high.toNat<4294967296) (middleSmall : middle.toNat<4294967296) (topSmall : top.toNat<4294967296)
    (highAtLeast : top.toNat≤high.toNat)
    (digitRange : (high.toNat*4294967296+middle.toNat)*4294967296+low.toNat<
      (top.toNat*4294967296+second.toNat)*4294967296) :
    let estimate:=((high<<<(32:Nat)) ||| middle)-(4294967295#64*top)
    4294967295*top.toNat+estimate.toNat=high.toNat*4294967296+middle.toNat ∧
      ((4294967295*top.toNat+estimate.toNat)*4294967296+low.toNat)/(top.toNat*4294967296+second.toNat)≤4294967295 := by
  have joined:=join_number high middle highSmall middleSmall
  have product : (4294967295#64*top).toNat=4294967295*top.toNat:=by
    rw [BitVec.toNat_mul]
    change (4294967295*top.toNat)%2^64=4294967295*top.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
  have before : (4294967295#64*top)≤((high<<<(32:Nat)) ||| middle):=by
    change (4294967295#64*top).toNat≤((high<<<(32:Nat)) ||| middle).toNat
    rw [product,joined]
    omega
  have difference:=BitVec.toNat_sub_of_le before
  rw [product,joined] at difference
  have conserved : 4294967295*top.toNat+(((high<<<(32:Nat)) ||| middle)-(4294967295#64*top)).toNat=
      high.toNat*4294967296+middle.toNat:=by omega
  refine ⟨conserved,?_⟩
  rw [conserved]
  have positive : 0<top.toNat*4294967296+second.toNat:=by omega
  have below : ((high.toNat*4294967296+middle.toNat)*4294967296+low.toNat)/(top.toNat*4294967296+second.toNat)<4294967296:=
    (Nat.div_lt_iff_lt_mul positive).mpr (by simpa only [Nat.mul_comm] using digitRange)
  omega

/-- The actual correction loop produces the exact quotient digit and full
remainder for the two-digit numerical case used by the Taylor denominator. -/
theorem normal_digit (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (q r top second low : BitVec 64)
    (ready : Bindings source q r 1#64 top second low)
    (topLarge : 2147483648≤top.toNat) (topSmall : top.toNat<4294967296)
    (qSmall : q.toNat<4294967296) (secondSmall : second.toNat<4294967296) (lowSmall : low.toNat<4294967296)
    (initialUpper : ((q.toNat*top.toNat+r.toNat)*4294967296+low.toNat)/(top.toNat*4294967296+second.toNat)≤q.toNat)
    (normal : evaluateHOLFiniteState source loop=(none,post)) :
    ∃ finalQ finalR corrections,corrections≤2 ∧ Bindings post finalQ finalR 0#64 top second low ∧
      finalQ.toNat=((q.toNat*top.toNat+r.toNat)*4294967296+low.toNat)/(top.toNat*4294967296+second.toNat) ∧
      finalR.toNat*4294967296+low.toNat-finalQ.toNat*second.toNat=
        ((q.toNat*top.toNat+r.toNat)*4294967296+low.toNat)%(top.toNat*4294967296+second.toNat) ∧
      finalR.toNat*4294967296+low.toNat-finalQ.toNat*second.toNat<top.toNat*4294967296+second.toNat ∧
      LocalEffects.erase post=LocalEffects.erase source := by
  obtain ⟨finalQ,finalR,corrections,bound,postReady,quotientHistory,remainderHistory,stopped,route,frame⟩:=
    loop_normal source post q r top second low ready topLarge topSmall normal
  have quotient:=route.quotient topLarge topSmall qSmall secondSmall lowSmall initialUpper stopped
  have finalSmall : finalQ.toNat<4294967296:=by omega
  have compared : finalQ.toNat*second.toNat≤finalR.toNat*4294967296+low.toNat:=by
    by_contra bad
    exact stopped ((corrects_iff finalQ finalR second low finalSmall secondSmall lowSmall).mpr (by omega))
  have conserved : finalQ.toNat*top.toNat+finalR.toNat=q.toNat*top.toNat+r.toNat:=by
    calc _=(finalQ.toNat+corrections)*top.toNat+r.toNat:=by rw [remainderHistory];ring
         _=q.toNat*top.toNat+r.toNat:=by rw [quotientHistory]
  let divisor:=top.toNat*4294967296+second.toNat
  let total:=(q.toNat*top.toNat+r.toNat)*4294967296+low.toNat
  let remaining:=finalR.toNat*4294967296+low.toNat-finalQ.toNat*second.toNat
  have positive : 0<divisor:=by dsimp [divisor];omega
  have addition : finalQ.toNat*divisor+remaining=total:=by
    have balance:=Nat.sub_add_cancel compared
    dsimp [remaining,divisor,total]
    rw [←conserved]
    nlinarith [balance]
  have standard:=Nat.mod_add_div total divisor
  change finalQ.toNat=total/divisor at quotient
  rw [←quotient] at standard
  have remainder : remaining=total%divisor:=by nlinarith [addition,standard]
  have remainderBound : remaining<divisor:=by rw [remainder];exact Nat.mod_lt _ positive
  exact ⟨finalQ,finalR,corrections,bound,postReady,quotient,remainder,remainderBound,frame⟩

end InitECandidate.Solver.Input.UDivMod.QhatCorrection

#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.max_initial_upper
#print axioms InitECandidate.Solver.Input.UDivMod.QhatCorrection.normal_digit

namespace InitECandidate.Solver.Input.UDivMod.TwoDigitSubtract
open Flapjack

def residual (cell carry product : BitVec 64) : BitVec 64:=cell-carry-(product &&& 4294967295#64)
def low (cell carry product : BitVec 64) : BitVec 64:=residual cell carry product &&& 4294967295#64
def nextCarry (cell carry product : BitVec 64) : BitVec 64:=
  (product>>>(32:Nat))-(residual cell carry product).sshiftRight 32

private theorem mask_number (word : BitVec 64) : (word &&& 4294967295#64).toNat=word.toNat%4294967296 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod word.toNat 32

private theorem high_number (word : BitVec 64) : (word>>>(32:Nat)).toNat=word.toNat/4294967296 := by
  rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

private theorem small_signed (word : BitVec 64) (small : word.toNat<4294967296) : word.toInt=(word.toNat : Int) :=
  BitVec.toInt_eq_toNat_of_lt (by omega)

/-- The actual signed intermediate of the original multiply/subtract loop
has no signed64-bit overflow, even when subtracting two full32-bit words. -/
theorem residual_signed (cell carry product : BitVec 64)
    (cellSmall : cell.toNat<4294967296) (carrySmall : carry.toNat<4294967296) :
    (residual cell carry product).toInt=(cell.toNat : Int)-carry.toNat-(product.toNat%4294967296) := by
  have productLow : (product &&& 4294967295#64).toNat<4294967296:=by
    rw [mask_number]
    exact Nat.mod_lt _ (by decide)
  have first : (cell-carry).toInt=(cell.toNat : Int)-carry.toNat:=by
    rw [BitVec.toInt_sub,small_signed cell cellSmall,small_signed carry carrySmall]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  rw [residual,BitVec.toInt_sub,first,small_signed _ productLow,mask_number]
  exact Int.bmod_eq_of_le (by have bound:=Nat.mod_lt product.toNat (show 0<4294967296 by decide);omega)
    (by have bound:=Nat.mod_lt product.toNat (show 0<4294967296 by decide);omega)

/-- Masking the actual signed residual keeps its ordinary base2^32 remainder. -/
theorem low_signed (cell carry product : BitVec 64) :
    ((low cell carry product).toNat : Int)=(residual cell carry product).toInt%4294967296 := by
  rw [low,mask_number,Int.natCast_emod,BitVec.toInt_eq_toNat_cond]
  split_ifs <;> omega

/-- One real32-bit multiply/subtract digit has a32-bit outgoing carry and
an exact conservation equation. The product cap follows from two32-bit factors. -/
theorem digit (cell carry product : BitVec 64)
    (cellSmall : cell.toNat<4294967296) (carrySmall : carry.toNat<4294967296)
    (productCap : product.toNat≤4294967295^2) :
    (low cell carry product).toNat<4294967296 ∧ (nextCarry cell carry product).toNat<4294967296 ∧
      cell.toNat+4294967296*(nextCarry cell carry product).toNat=
        (low cell carry product).toNat+product.toNat+carry.toNat := by
  have masked : (low cell carry product).toNat<4294967296:=by
    rw [low,mask_number]
    exact Nat.mod_lt _ (by decide)
  have high:=high_number product
  have productLow:=Nat.mod_lt product.toNat (show 0<4294967296 by decide)
  have splitProduct:=Nat.mod_add_div product.toNat 4294967296
  have signed:=residual_signed cell carry product cellSmall carrySmall
  have shifted : ((residual cell carry product).sshiftRight 32).toInt=
      (residual cell carry product).toInt/4294967296:=by
    rw [BitVec.toInt_sshiftRight,Int.shiftRight_eq_div_pow]
    rfl
  have highSmall : (product>>>(32:Nat)).toNat<4294967296:=by omega
  have outgoing : (nextCarry cell carry product).toInt=
      ((product>>>(32:Nat)).toNat : Int)-(residual cell carry product).toInt/4294967296:=by
    rw [nextCarry,BitVec.toInt_sub,small_signed _ highSmall,shifted]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have lowEq:=low_signed cell carry product
  have balance:=Int.emod_add_mul_ediv (residual cell carry product).toInt 4294967296
  have nonnegative : 0≤(nextCarry cell carry product).toInt:=by omega
  have natural : (nextCarry cell carry product).toInt=((nextCarry cell carry product).toNat : Int):=by
    have conversion:=BitVec.toInt_eq_toNat_cond (nextCarry cell carry product)
    have bounded:=(nextCarry cell carry product).isLt
    split_ifs at conversion <;> omega
  refine ⟨masked,?_,?_⟩ <;> omega

end InitECandidate.Solver.Input.UDivMod.TwoDigitSubtract

#print axioms InitECandidate.Solver.Input.UDivMod.TwoDigitSubtract.residual_signed
#print axioms InitECandidate.Solver.Input.UDivMod.TwoDigitSubtract.low_signed
#print axioms InitECandidate.Solver.Input.UDivMod.TwoDigitSubtract.digit

namespace InitECandidate.Solver.Input.UDivMod.TwoDigitSubtract
open Flapjack

/-- The original64-bit word multiplication of two32-bit digits is exact
and supplies the cap used by the real subtraction/carry step. -/
theorem product_number (left right : BitVec 64) (leftSmall : left.toNat<4294967296) (rightSmall : right.toNat<4294967296) :
    (left*right).toNat=left.toNat*right.toNat ∧ (left*right).toNat≤4294967295^2 := by
  have bound : left.toNat*right.toNat≤4294967295^2:=by
    change left.toNat*right.toNat≤4294967295*4294967295
    exact Nat.mul_le_mul (by omega) (by omega)
  have number : (left*right).toNat=left.toNat*right.toNat:=by
    rw [BitVec.toNat_mul,Nat.mod_eq_of_lt (by omega)]
  exact ⟨number,by omega⟩

theorem product_digit (cell carry quotient divisor : BitVec 64)
    (cellSmall : cell.toNat<4294967296) (carrySmall : carry.toNat<4294967296)
    (quotientSmall : quotient.toNat<4294967296) (divisorSmall : divisor.toNat<4294967296) :
    (low cell carry (quotient*divisor)).toNat<4294967296 ∧
      (nextCarry cell carry (quotient*divisor)).toNat<4294967296 ∧
      cell.toNat+4294967296*(nextCarry cell carry (quotient*divisor)).toNat=
        (low cell carry (quotient*divisor)).toNat+quotient.toNat*divisor.toNat+carry.toNat := by
  have number:=product_number quotient divisor quotientSmall divisorSmall
  obtain ⟨lowSmall,carryOutSmall,balance⟩:=digit cell carry (quotient*divisor) cellSmall carrySmall number.2
  rw [number.1] at balance
  exact ⟨lowSmall,carryOutSmall,balance⟩

def firstCarry (lowCell quotient lowDivisor : BitVec 64) : BitVec 64:=nextCarry lowCell 0#64 (quotient*lowDivisor)
def secondCarry (lowCell middleCell quotient lowDivisor highDivisor : BitVec 64) : BitVec 64:=
  nextCarry middleCell (firstCarry lowCell quotient lowDivisor) (quotient*highDivisor)
def firstLow (lowCell quotient lowDivisor : BitVec 64) : BitVec 64:=low lowCell 0#64 (quotient*lowDivisor)
def secondLow (lowCell middleCell quotient lowDivisor highDivisor : BitVec 64) : BitVec 64:=
  low middleCell (firstCarry lowCell quotient lowDivisor) (quotient*highDivisor)

def window (lowCell middleCell topCell : BitVec 64) : Nat:=lowCell.toNat+4294967296*middleCell.toNat+18446744073709551616*topCell.toNat
def divisorNumber (lowDivisor highDivisor : BitVec 64) : Nat:=lowDivisor.toNat+4294967296*highDivisor.toNat

/-- Two real subtraction digits with a correct quotient leave a zero top
word. Thus the original add-back test is false once its actual inputs and
corrected quotient have been connected to this equation. -/
theorem pair_no_borrow (lowCell middleCell topCell quotient lowDivisor highDivisor : BitVec 64)
    (lowSmall : lowCell.toNat<4294967296) (middleSmall : middleCell.toNat<4294967296)
    (quotientSmall : quotient.toNat<4294967296) (divisorLowSmall : lowDivisor.toNat<4294967296) (divisorHighSmall : highDivisor.toNat<4294967296)
    (below : quotient.toNat*divisorNumber lowDivisor highDivisor≤window lowCell middleCell topCell)
    (close : window lowCell middleCell topCell<quotient.toNat*divisorNumber lowDivisor highDivisor+18446744073709551616) :
    secondCarry lowCell middleCell quotient lowDivisor highDivisor=topCell ∧
      topCell-secondCarry lowCell middleCell quotient lowDivisor highDivisor=0#64 ∧
      (firstLow lowCell quotient lowDivisor).toNat+4294967296*(secondLow lowCell middleCell quotient lowDivisor highDivisor).toNat=
        window lowCell middleCell topCell-quotient.toNat*divisorNumber lowDivisor highDivisor := by
  have first:=product_digit lowCell 0#64 quotient lowDivisor lowSmall (by decide) quotientSmall divisorLowSmall
  have second:=product_digit middleCell (firstCarry lowCell quotient lowDivisor) quotient highDivisor middleSmall first.2.1 quotientSmall divisorHighSmall
  have distributed : quotient.toNat*divisorNumber lowDivisor highDivisor=
      quotient.toNat*lowDivisor.toNat+4294967296*(quotient.toNat*highDivisor.toNat):=by
    unfold divisorNumber
    ring
  change (firstLow lowCell quotient lowDivisor).toNat<4294967296 ∧ (firstCarry lowCell quotient lowDivisor).toNat<4294967296 ∧
    lowCell.toNat+4294967296*(firstCarry lowCell quotient lowDivisor).toNat=(firstLow lowCell quotient lowDivisor).toNat+quotient.toNat*lowDivisor.toNat+0 at first
  change (secondLow lowCell middleCell quotient lowDivisor highDivisor).toNat<4294967296 ∧
    (secondCarry lowCell middleCell quotient lowDivisor highDivisor).toNat<4294967296 ∧
    middleCell.toNat+4294967296*(secondCarry lowCell middleCell quotient lowDivisor highDivisor).toNat=
      (secondLow lowCell middleCell quotient lowDivisor highDivisor).toNat+quotient.toNat*highDivisor.toNat+(firstCarry lowCell quotient lowDivisor).toNat at second
  rw [distributed] at below close ⊢
  unfold window at below close ⊢
  have same : secondCarry lowCell middleCell quotient lowDivisor highDivisor=topCell:=by
    apply BitVec.eq_of_toNat_eq
    omega
  refine ⟨same,by rw [same];simp,?_⟩
  have firstBalance:=first.2.2
  have secondBalance:=second.2.2
  rw [same] at secondBalance
  omega

/-- The actual exact quotient suffices for both no-borrow conditions and
identifies the two stored low words with the ordinary natural remainder. -/
theorem pair_from_quotient (lowCell middleCell topCell quotient lowDivisor highDivisor : BitVec 64)
    (lowSmall : lowCell.toNat<4294967296) (middleSmall : middleCell.toNat<4294967296)
    (quotientSmall : quotient.toNat<4294967296) (divisorLowSmall : lowDivisor.toNat<4294967296) (divisorHighSmall : highDivisor.toNat<4294967296)
    (positive : 0<divisorNumber lowDivisor highDivisor)
    (exactQuotient : quotient.toNat=window lowCell middleCell topCell/divisorNumber lowDivisor highDivisor) :
    secondCarry lowCell middleCell quotient lowDivisor highDivisor=topCell ∧
      topCell-secondCarry lowCell middleCell quotient lowDivisor highDivisor=0#64 ∧
      (firstLow lowCell quotient lowDivisor).toNat+4294967296*(secondLow lowCell middleCell quotient lowDivisor highDivisor).toNat=
        window lowCell middleCell topCell%divisorNumber lowDivisor highDivisor := by
  have decomposition:=Nat.mod_add_div (window lowCell middleCell topCell) (divisorNumber lowDivisor highDivisor)
  rw [←exactQuotient,Nat.mul_comm (divisorNumber lowDivisor highDivisor) quotient.toNat] at decomposition
  have small:=Nat.mod_lt (window lowCell middleCell topCell) positive
  have width : divisorNumber lowDivisor highDivisor<18446744073709551616:=by unfold divisorNumber;omega
  obtain ⟨same,topZero,remainder⟩:=pair_no_borrow lowCell middleCell topCell quotient lowDivisor highDivisor
    lowSmall middleSmall quotientSmall divisorLowSmall divisorHighSmall (by omega) (by omega)
  exact ⟨same,topZero,by omega⟩

end InitECandidate.Solver.Input.UDivMod.TwoDigitSubtract

#print axioms InitECandidate.Solver.Input.UDivMod.TwoDigitSubtract.product_number
#print axioms InitECandidate.Solver.Input.UDivMod.TwoDigitSubtract.product_digit
#print axioms InitECandidate.Solver.Input.UDivMod.TwoDigitSubtract.pair_no_borrow
#print axioms InitECandidate.Solver.Input.UDivMod.TwoDigitSubtract.pair_from_quotient

namespace InitECandidate.Solver.Input.UDivMod.Normalize
open Flapjack

def high (word : BitVec 64) (bits : Nat) : BitVec 64:=word>>>(32-bits)
def digit (current previous : BitVec 64) (bits : Nat) : BitVec 64:=
  ((current<<<bits) ||| high previous bits) &&& 4294967295#64
def first (word : BitVec 64) (bits : Nat) : BitVec 64:=(word<<<bits) &&& 4294967295#64

theorem high_number (word : BitVec 64) (bits : Nat) :
    (high word bits).toNat=word.toNat/2^(32-bits) := by
  rw [high,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

private theorem powers (bits : Nat) (small : bits≤31) : 2^(32-bits)*2^bits=4294967296 := by
  rw [←Nat.pow_add]
  have exponents : 32-bits+bits=32:=by omega
  rw [exponents]

/-- The actual right-shifted carry fits below the normalization power. -/
theorem high_bound (word : BitVec 64) (bits : Nat) (small : bits≤31) (wordSmall : word.toNat<4294967296) :
    (high word bits).toNat<2^bits := by
  have positive : 0<2^(32-bits):=Nat.two_pow_pos _
  rw [high_number,Nat.div_lt_iff_lt_mul positive]
  have power:=powers bits small
  rw [Nat.mul_comm] at power
  omega

private theorem shifted_number (word : BitVec 64) (bits : Nat) (small : bits≤31) (wordSmall : word.toNat<4294967296) :
    (word<<<bits).toNat=word.toNat*2^bits := by
  have factorBound : 2^bits≤2147483648:=Nat.pow_le_pow_right (by decide) small
  have productBound:=Nat.mul_le_mul (show word.toNat≤4294967295 by omega) factorBound
  rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.mod_eq_of_lt (by omega)]

private theorem joined_number (current previous : BitVec 64) (bits : Nat) (small : bits≤31)
    (currentSmall : current.toNat<4294967296) (previousSmall : previous.toNat<4294967296) :
    ((current<<<bits) ||| high previous bits).toNat=current.toNat*2^bits+(high previous bits).toNat := by
  rw [BitVec.toNat_or,shifted_number current bits small currentSmall]
  have joined:=Nat.two_pow_add_eq_or_of_lt (i:=bits) (high_bound previous bits small previousSmall) current.toNat
  rw [Nat.mul_comm current.toNat (2^bits)]
  exact joined.symm

private theorem masked_number (word : BitVec 64) : (word &&& 4294967295#64).toNat=word.toNat%4294967296 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod word.toNat 32

/-- Actual shift/or/mask normalization has an exact carry equation. Both
input words are original32-bit digits; all64-bit intermediate shifts are exact. -/
theorem digit_balance (current previous : BitVec 64) (bits : Nat) (small : bits≤31)
    (currentSmall : current.toNat<4294967296) (previousSmall : previous.toNat<4294967296) :
    (digit current previous bits).toNat<4294967296 ∧
      (digit current previous bits).toNat+4294967296*(high current bits).toNat=
        current.toNat*2^bits+(high previous bits).toNat := by
  have upper:=high_bound previous bits small previousSmall
  have positive : 0<2^(32-bits):=Nat.two_pow_pos _
  have remainderBound:=Nat.mod_lt current.toNat positive
  have decomposition:=Nat.mod_add_div current.toNat (2^(32-bits))
  have power:=powers bits small
  have next : current.toNat%2^(32-bits)+1≤2^(32-bits):=by omega
  have weighted:=Nat.mul_le_mul_right (2^bits) next
  rw [Nat.add_mul,Nat.one_mul,power] at weighted
  have lowBound : (current.toNat%2^(32-bits))*2^bits+(high previous bits).toNat<4294967296:=by omega
  have splitScaled : current.toNat*2^bits+(high previous bits).toNat=
      (current.toNat%2^(32-bits))*2^bits+(high previous bits).toNat+4294967296*(current.toNat/2^(32-bits)):=by
    calc
      _=(current.toNat%2^(32-bits)+2^(32-bits)*(current.toNat/2^(32-bits)))*2^bits+(high previous bits).toNat:=by rw [decomposition]
      _=(current.toNat%2^(32-bits))*2^bits+(high previous bits).toNat+(2^(32-bits)*2^bits)*(current.toNat/2^(32-bits)):=by ring
      _=_:=by rw [power]
  have digitNumber : (digit current previous bits).toNat=(current.toNat*2^bits+(high previous bits).toNat)%4294967296:=by
    rw [digit,masked_number,joined_number current previous bits small currentSmall previousSmall]
  have bounded:=Nat.mod_lt (current.toNat*2^bits+(high previous bits).toNat) (show 0<4294967296 by decide)
  rw [digitNumber,high_number current bits]
  exact ⟨bounded,by omega⟩

/-- The original separate lowest-word store is the same normalization with
zero incoming carry. -/
theorem first_balance (word : BitVec 64) (bits : Nat) (small : bits≤31) (wordSmall : word.toNat<4294967296) :
    (first word bits).toNat<4294967296 ∧
      (first word bits).toNat+4294967296*(high word bits).toNat=word.toNat*2^bits := by
  simpa [digit,high,first] using digit_balance word 0#64 bits small wordSmall (by decide)

end InitECandidate.Solver.Input.UDivMod.Normalize

#print axioms InitECandidate.Solver.Input.UDivMod.Normalize.high_number
#print axioms InitECandidate.Solver.Input.UDivMod.Normalize.high_bound
#print axioms InitECandidate.Solver.Input.UDivMod.Normalize.digit_balance
#print axioms InitECandidate.Solver.Input.UDivMod.Normalize.first_balance

namespace InitECandidate.Solver.Input.UDivMod.Normalize
open Flapjack

/-- A normalized leading digit whose shifted value is below the radix has
no discarded outgoing carry. This is the genuine nlz32 caller's upper bound. -/
theorem high_zero (word : BitVec 64) (bits : Nat) (small : bits≤31)
    (upper : word.toNat*2^bits<4294967296) : high word bits=0#64 := by
  have power:=powers bits small
  have inside : word.toNat<2^(32-bits):=by
    by_contra outside
    have lower:=Nat.mul_le_mul_right (2^bits) (show 2^(32-bits)≤word.toNat by omega)
    rw [power] at lower
    omega
  apply BitVec.eq_of_toNat_eq
  rw [high_number,Nat.div_eq_of_lt inside]
  rfl

end InitECandidate.Solver.Input.UDivMod.Normalize

#print axioms InitECandidate.Solver.Input.UDivMod.Normalize.high_zero
