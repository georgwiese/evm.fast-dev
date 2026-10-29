import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.Input.ClockCostCurrentScoped
import InitECandidate.Solver.Input.LocalEffectsCurrentScoped
import InitECandidate.Solver.Input.ScopedCallNormal
import InitECandidate.Solver.Input.ReturnNormal
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.PureReturn
import InitECandidate.Solver.GasBudget.ArithmeticClockPrice
import InitECandidate.Solver.Input.RlpWrite.U256Value

namespace InitECandidate.Solver.GasBudget.U256Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
abbrev Quad := Input.RlpWrite.U256Value.Words
def body : ProgHOL 64 := match Guest.guestFn_u256_is_zero with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "a",Input.RlpWrite.U256Value.tupleShape)]
def mixed (words : Quad) : BitVec 64 := words 0 ||| (words 1 ||| (words 2 ||| words 3))
def resultWord (words : Quad) : BitVec 64 := if mixed words=0#64 then 1#64 else 0#64

theorem mixed_zero (words : Quad) : mixed words=0#64 ↔ ∀ index,words index=0#64 := by
  simp only [mixed,BitVec.or_eq_zero_iff]
  constructor
  · rintro ⟨a,b,c,d⟩ index
    have choices : index.val=0 ∨ index.val=1 ∨ index.val=2 ∨ index.val=3 := by have h:=index.isLt; omega
    rcases choices with h|h|h|h
    all_goals have equal : index=⟨index.val,index.isLt⟩:=rfl
    all_goals cases index; simp_all
  · intro zero
    exact ⟨zero 0,zero 1,zero 2,zero 3⟩

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : Quad)
    (a : source.locals.lookup (ofString "a")=some (Input.RlpWrite.U256Value.tuple words)) :
    evaluateHOLFiniteState source body=(some (.returned (.val (.word (resultWord words)))),emptyLocalsHOLFinite source) := by
  classical
  have folded : OrOp.or (words 0) (OrOp.or (words 1) (OrOp.or (words 2) (OrOp.or (words 3) 0#64)))=mixed words := by
    change words 0 ||| (words 1 ||| (words 2 ||| (words 3 ||| 0#64)))=mixed words
    simp [mixed]
  by_cases zero : mixed words=0#64
  all_goals simp [body,Guest.guestFn_u256_is_zero,progToHOL,expToHOL,resultWord,evaluateHOLFiniteState_seq,
    evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,a,Input.RlpWrite.U256Value.tuple,
    valueIsWord,valueWord,wordOpHOL,wordOp,folded,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero,shapeOfHOLExact,
    sizeOfShapeWithContextHOL,fixClockHOLFinite,emptyLocalsHOLFinite]

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : Quad)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [Input.RlpWrite.U256Value.tuple words])
    (code : source.code.lookup (ofString "u256_is_zero")=some (formals,body,.one)) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "u256_is_zero") expressions continuation)=
      (let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1} name (resultWord words)) continuation
      (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,a⟩:=Input.RlpWrite.U256Value.environment source.code.lookup (ofString "u256_is_zero") body words code
  let entry:=callEntryStateHOLFinite source callee
  have run:=execute entry words a
  have actual:=Input.CallNormal.pure_return_execute source (emptyLocalsHOLFinite entry) name (ofString "u256_is_zero") expressions [Input.RlpWrite.U256Value.tuple words]
    body continuation callee (resultWord words) 0 args called enough run rfl
  simpa only [Nat.sub_zero] using actual

end InitECandidate.Solver.GasBudget.U256Zero

#print axioms InitECandidate.Solver.GasBudget.U256Zero.mixed_zero
#print axioms InitECandidate.Solver.GasBudget.U256Zero.execute
#print axioms InitECandidate.Solver.GasBudget.U256Zero.call_execute


namespace InitECandidate.Solver.GasBudget.U256Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem current_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "u256_is_zero")=some (formals,body,.one) := by
  have known:=ArithmeticEffects.current_environment code installed .u256_is_zero
  simpa only [ArithmeticEffects.Kind.name,ArithmeticEffects.Kind.signature,ArithmeticEffects.Kind.original,
    body,formals,Input.RlpWrite.U256Value.tupleShape,Guest.guestFn_u256_is_zero,shapeToHOL,List.map_cons,List.map_nil] using known

end InitECandidate.Solver.GasBudget.U256Zero

#print axioms InitECandidate.Solver.GasBudget.U256Zero.current_code

namespace InitECandidate.Solver.GasBudget.U256Zero

/-- Little-endian natural value of the actual four64-bit scalar limbs. -/
def number (words : Quad) : Nat:=
  (words 0).toNat+2^64*(words 1).toNat+2^128*(words 2).toNat+2^192*(words 3).toNat

theorem number_lt (words : Quad) : number words<2^256 := by
  have first:=(words 0).isLt
  have second:=(words 1).isLt
  have third:=(words 2).isLt
  have fourth:=(words 3).isLt
  unfold number
  omega

theorem number_zero (words : Quad) : number words=0 ↔ ∀ index,words index=0#64 := by
  constructor
  · intro zero index
    unfold number at zero
    obtain ⟨index,inside⟩:=index
    have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3:=by omega
    rcases cases with rfl|rfl|rfl|rfl
    · apply BitVec.eq_of_toNat_eq
      change (words 0).toNat=0
      omega
    · apply BitVec.eq_of_toNat_eq
      change (words 1).toNat=0
      omega
    · apply BitVec.eq_of_toNat_eq
      change (words 2).toNat=0
      omega
    · apply BitVec.eq_of_toNat_eq
      change (words 3).toNat=0
      omega
  · intro zero
    simp [number,zero]

theorem mixed_number_zero (words : Quad) : mixed words=0#64 ↔ number words=0 :=
  (mixed_zero words).trans (number_zero words).symm

/-- The real software zero-test result is zero exactly when its current
256-bit natural value is positive. This supplies the actual Taylor guard. -/
theorem resultWord_zero (words : Quad) : resultWord words=0#64 ↔ 0<number words := by
  constructor
  · intro active
    by_cases zero : number words=0
    · have allZero:=(mixed_number_zero words).mpr zero
      simp [resultWord,allZero] at active
    · omega
  · intro positive
    have nonzero : mixed words≠0#64:=by
      intro zero
      have valueZero:=(mixed_number_zero words).mp zero
      omega
    simp [resultWord,nonzero]

end InitECandidate.Solver.GasBudget.U256Zero

#print axioms InitECandidate.Solver.GasBudget.U256Zero.number_lt
#print axioms InitECandidate.Solver.GasBudget.U256Zero.number_zero
#print axioms InitECandidate.Solver.GasBudget.U256Zero.mixed_number_zero
#print axioms InitECandidate.Solver.GasBudget.U256Zero.resultWord_zero

namespace InitECandidate.Solver.GasBudget.U256Division
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
abbrev Quad:=U256Zero.Quad

def divmodBody : ProgHOL 64:=match Guest.Software.guestFn_u256_divmod with | .function fn=>progToHOL fn.body | _=>.skip
def divBody : ProgHOL 64:=match Guest.Software.guestFn_u256_div with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "a",Input.RlpWrite.U256Value.tupleShape),(ofString "b",Input.RlpWrite.U256Value.tupleShape)]
def shapeEight : ShapeHOL:=.comb [.one,.one,.one,.one,.one,.one,.one,.one]
def zeroWords : Quad:=fun _=>0#64
def zeroEight : ValueHOL 64:=.rStruct [.val (.word 0#64),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64),
  .val (.word 0#64),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)]
def zeroEightExpression : ExpHOL 64:=.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64,.const 0#64,.const 0#64,.const 0#64,.const 0#64]
def divisorTest : ExpHOL 64:=.cmp .equal (.op .or [.rfield 0 (localVar "b"),.rfield 1 (localVar "b"),.rfield 2 (localVar "b"),.rfield 3 (localVar "b")]) (.const 0#64)
def divmodTail : ProgHOL 64:=match divmodBody with | .seq _ rest=>rest | _=>.skip

theorem divmod_shape : divmodBody=.seq (.ite divisorTest (.return zeroEightExpression) .skip) divmodTail := by
  simp only [divmodBody,divmodTail,divisorTest,zeroEightExpression,Guest.Software.guestFn_u256_divmod,progToHOL,expToHOL,shapeToHOL,
    localVar,List.map_cons,List.map_nil,Option.map_none,Option.map_some]

set_option maxRecDepth 100000 in
theorem divmod_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "u256_divmod")=some (formals,divmodBody,shapeEight) := by
  have found:=Input.OriginalCode.indexed code installed 63 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_u256_divmod) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,divmodBody,shapeEight,
    Input.RlpWrite.U256Value.tupleShape,Guest.Software.guestFn_u256_divmod,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using found

set_option maxRecDepth 100000 in
theorem div_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "u256_div")=some (formals,divBody,Input.RlpWrite.U256Value.tupleShape) := by
  have found:=Input.OriginalCode.indexed code installed 64 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_u256_div) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,divBody,
    Input.RlpWrite.U256Value.tupleShape,Guest.Software.guestFn_u256_div,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using found

/-- The actual original wide division checks zero before reading its
numerator, using its workspace or entering any numerical division helper. -/
theorem divmod_zero_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (divisor : source.locals.lookup (ofString "b")=some (Input.RlpWrite.U256Value.tuple zeroWords)) :
    evaluateHOLFiniteState source divmodBody=(some (.returned zeroEight),emptyLocalsHOLFinite source) := by
  have read : eval source divisorTest=some (.val (.word 1#64)):=by
    simp [eval,divisorTest,evalHOLExact,evalListHOLExact,toExact,localVar,divisor,Input.RlpWrite.U256Value.tuple,zeroWords,
      valueIsWord,valueWord,wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    change (0#64 : BitVec 64) ||| (0#64 ||| (0#64 ||| (0#64 ||| 0#64)))=0#64
    rfl
  rw [divmod_shape,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  simp only [eval] at read
  rw [read]
  simp [evaluateHOLFiniteState_return,zeroEightExpression,zeroEight,evalHOLExact,evalListHOLExact,shapeOfHOLExact,
    sizeOfShapeWithContextHOL,fixClockHOLFinite,emptyLocalsHOLFinite]

theorem divmod_zero_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (divisor : source.locals.lookup (ofString "b")=some (Input.RlpWrite.U256Value.tuple zeroWords)) :
    source.clock-(evaluateHOLFiniteState source divmodBody).2.clock≤0 := by
  rw [divmod_zero_execute source divisor]
  simp [emptyLocalsHOLFinite]

end InitECandidate.Solver.GasBudget.U256Division

#print axioms InitECandidate.Solver.GasBudget.U256Division.divmod_shape
#print axioms InitECandidate.Solver.GasBudget.U256Division.divmod_code
#print axioms InitECandidate.Solver.GasBudget.U256Division.div_code
#print axioms InitECandidate.Solver.GasBudget.U256Division.divmod_zero_execute
#print axioms InitECandidate.Solver.GasBudget.U256Division.divmod_zero_cost

namespace InitECandidate.Solver.Input.RlpWrite.U256Value
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual common two-quadruple signature determines both checked
callee values, for any original function name, body and returned shape. -/
theorem pair_environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (function : MlS) (body : ProgHOL 64) (returnShape : ShapeHOL) (a b : Words)
    (lookup : codeFn function=some ([(ofString "a",tupleShape),(ofString "b",tupleShape)],body,returnShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn function [tuple a,tuple b]=some (body,callee,returnShape) ∧
      callee.lookup (ofString "a")=some (tuple a) ∧ callee.lookup (ofString "b")=some (tuple b) := by
  let formals : List (MlS×ShapeHOL):=[(ofString "a",tupleShape),(ofString "b",tupleShape)]
  let values : List (ValueHOL 64):=[tuple a,tuple b]
  let rawLocals : MlS→Option (ValueHOL 64):=fun name=>if name=ofString "b" then some (tuple b) else if name=ofString "a" then some (tuple a) else none
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=values.length ∧
      ((formals.zip values).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true:=by
    simp [formals,values,tuple,tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true,show ofString "a"≠ofString "b" from by decide]
  have raw : lookupCodeHOLExact codeFn function values=some (body,rawLocals,returnShape):=by
    change codeFn function=some (formals,body,returnShape) at lookup
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,show ofString "a"≠ofString "b" from by decide],by rw [locals]; simp [rawLocals]⟩

end InitECandidate.Solver.Input.RlpWrite.U256Value

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Value.pair_environment

namespace InitECandidate.Solver.GasBudget.U256Division
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def divArguments : List (ExpHOL 64):=[localVar "a",localVar "b"]
def quotientExpression : ExpHOL 64:=.rstruct [.rfield 0 (localVar "qr"),.rfield 1 (localVar "qr"),.rfield 2 (localVar "qr"),.rfield 3 (localVar "qr")]
def divReturn : ProgHOL 64:=.return quotientExpression

theorem div_shape : divBody=.decCall (ofString "qr") shapeEight (ofString "u256_divmod") divArguments divReturn := by
  simp only [divBody,divArguments,divReturn,quotientExpression,shapeEight,Guest.Software.guestFn_u256_div,progToHOL,expToHOL,shapeToHOL,
    localVar,List.map_cons,List.map_nil]

theorem zero_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (numerator : Quad)
    (a : source.locals.lookup (ofString "a")=some (Input.RlpWrite.U256Value.tuple numerator))
    (b : source.locals.lookup (ofString "b")=some (Input.RlpWrite.U256Value.tuple zeroWords))
    (installed : Input.OriginalCode.Installed source.code) :
    ∃ callee,evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) divArguments=
      some [Input.RlpWrite.U256Value.tuple numerator,Input.RlpWrite.U256Value.tuple zeroWords] ∧
      lookupCodeHOLFinite source.code.lookup (ofString "u256_divmod") [Input.RlpWrite.U256Value.tuple numerator,Input.RlpWrite.U256Value.tuple zeroWords]=some (divmodBody,callee,shapeEight) ∧
      callee.lookup (ofString "b")=some (Input.RlpWrite.U256Value.tuple zeroWords) := by
  obtain ⟨callee,called,aCell,bCell⟩:=Input.RlpWrite.U256Value.pair_environment source.code.lookup (ofString "u256_divmod") divmodBody shapeEight numerator zeroWords
    (divmod_code source.code installed)
  refine ⟨callee,?_,called,bCell⟩
  simp [divArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,a,b]

/-- Every actual zero-divisor wrapper outcome costs at most its one real
helper-call tick, including a caller timeout at clock0. -/
theorem div_zero_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (numerator : Quad)
    (a : source.locals.lookup (ofString "a")=some (Input.RlpWrite.U256Value.tuple numerator))
    (b : source.locals.lookup (ofString "b")=some (Input.RlpWrite.U256Value.tuple zeroWords))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source divBody).2.clock≤1 := by
  obtain ⟨callee,args,called,bCell⟩:=zero_entry source numerator a b installed
  rw [div_shape]
  exact Input.ClockCost.scoped_current source (ofString "qr") shapeEight (ofString "u256_divmod") divArguments _ divmodBody divReturn callee shapeEight 0 0 args called
    (divmod_zero_cost (callEntryStateHOLFinite source callee) bCell) (Input.ClockCost.returned source.code _)

theorem div_zero_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (numerator : Quad)
    (a : source.locals.lookup (ofString "a")=some (Input.RlpWrite.U256Value.tuple numerator))
    (b : source.locals.lookup (ofString "b")=some (Input.RlpWrite.U256Value.tuple zeroWords))
    (installed : Input.OriginalCode.Installed source.code) :
    Input.LocalEffects.erase (evaluateHOLFiniteState source divBody).2=Input.LocalEffects.erase source := by
  obtain ⟨callee,args,called,bCell⟩:=zero_entry source numerator a b installed
  have frame : Input.LocalEffects.erase (evaluateHOLFiniteState (callEntryStateHOLFinite source callee) divmodBody).2=Input.LocalEffects.erase source:=by
    rw [divmod_zero_execute (callEntryStateHOLFinite source callee) bCell]
    rfl
  rw [div_shape]
  exact Input.LocalEffects.scoped_current source (ofString "qr") shapeEight (ofString "u256_divmod") divArguments _ divmodBody divReturn callee shapeEight args called frame
    (Input.LocalEffects.returned source.code _)

/-- A real normal wrapper return receives the actual checked zero remainder/
quotient tuple, so its four selected quotient limbs are genuinely zero. -/
theorem div_zero_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (numerator : Quad)
    (a : source.locals.lookup (ofString "a")=some (Input.RlpWrite.U256Value.tuple numerator))
    (b : source.locals.lookup (ofString "b")=some (Input.RlpWrite.U256Value.tuple zeroWords))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source divBody=(some (.returned value),post)) :
    value=Input.RlpWrite.U256Value.tuple zeroWords := by
  obtain ⟨callee,args,called,bCell⟩:=zero_entry source numerator a b installed
  rw [div_shape] at normal
  obtain ⟨funded,child,returned,inner,bodyRun,checked,remaining,endpoint⟩:=Input.CallNormal.scoped_normal source post "qr" shapeEight
    (ofString "u256_divmod") divArguments _ divmodBody divReturn callee shapeEight args called value normal
  rw [divmod_zero_execute (callEntryStateHOLFinite source callee) bCell] at bodyRun
  have resultEq:=congrArg Prod.fst bodyRun
  have answer : returned=zeroEight:=by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using resultEq.symm
  let current:=Input.CallNormal.continuationEntry source child "qr" returned
  have qrCell : current.locals.lookup (ofString "qr")=some zeroEight:=by
    rw [←answer]
    exact Input.CallNormal.continuation_lookup_same _ _ _ _
  obtain ⟨read,postEq⟩:=Input.return_normal current inner quotientExpression value remaining
  have expected : eval current quotientExpression=some (Input.RlpWrite.U256Value.tuple zeroWords):=by
    simp [eval,quotientExpression,evalHOLExact,evalListHOLExact,toExact,localVar,qrCell,zeroEight,Input.RlpWrite.U256Value.tuple,zeroWords]
  exact Option.some.inj (read.symm.trans expected)

end InitECandidate.Solver.GasBudget.U256Division

#print axioms InitECandidate.Solver.GasBudget.U256Division.div_shape
#print axioms InitECandidate.Solver.GasBudget.U256Division.zero_entry
#print axioms InitECandidate.Solver.GasBudget.U256Division.div_zero_cost
#print axioms InitECandidate.Solver.GasBudget.U256Division.div_zero_frame
#print axioms InitECandidate.Solver.GasBudget.U256Division.div_zero_normal
