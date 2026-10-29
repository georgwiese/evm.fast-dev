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
