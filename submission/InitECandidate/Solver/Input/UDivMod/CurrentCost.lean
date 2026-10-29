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
