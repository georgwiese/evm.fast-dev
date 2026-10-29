import InitECandidate.Solver.GasBudget.U256Eq
import InitECandidate.Solver.Input.OriginalEntry

namespace InitECandidate.Solver.GasBudget.U256LessThan
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
abbrev Quad := Input.RlpWrite.U256Value.Words
def body : ProgHOL 64 := match Guest.guestFn_u256_lt with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := U256Eq.formals
def resultWord (a b : Quad) : BitVec 64 :=
  if (if a 3 ≠ b 3 then a 3 < b 3 else if a 2 ≠ b 2 then a 2 < b 2 else if a 1 ≠ b 1 then a 1 < b 1 else a 0 < b 0) then 1#64 else 0#64

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : Quad)
    (aLocal : source.locals.lookup (ofString "a") = some (Input.RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b") = some (Input.RlpWrite.U256Value.tuple b)) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word (resultWord a b)))),emptyLocalsHOLFinite source) := by
  classical
  by_cases same3 : a 3 = b 3
  · by_cases same2 : a 2 = b 2
    · by_cases same1 : a 1 = b 1
      · by_cases lower : a 0 < b 0
        all_goals simp [body,Guest.guestFn_u256_lt,progToHOL,expToHOL,shapeToHOL,resultWord,
          evaluateHOLFiniteState_seq,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,evaluateHOLFiniteState_skip,
          evalHOLExact,evalListHOLExact,toExact,aLocal,bLocal,Input.RlpWrite.U256Value.tuple,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL,same3,same2,same1,lower,fixClockHOLFinite,shapeOfHOLExact,emptyLocalsHOLFinite]
      · by_cases lower : a 1 < b 1
        all_goals simp [body,Guest.guestFn_u256_lt,progToHOL,expToHOL,shapeToHOL,resultWord,
          evaluateHOLFiniteState_seq,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,evaluateHOLFiniteState_skip,
          evalHOLExact,evalListHOLExact,toExact,aLocal,bLocal,Input.RlpWrite.U256Value.tuple,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL,same3,same2,same1,lower,fixClockHOLFinite,shapeOfHOLExact,emptyLocalsHOLFinite]
    · by_cases lower : a 2 < b 2
      all_goals simp [body,Guest.guestFn_u256_lt,progToHOL,expToHOL,shapeToHOL,resultWord,
        evaluateHOLFiniteState_seq,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,evaluateHOLFiniteState_skip,
        evalHOLExact,evalListHOLExact,toExact,aLocal,bLocal,Input.RlpWrite.U256Value.tuple,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,same3,same2,lower,fixClockHOLFinite,shapeOfHOLExact,emptyLocalsHOLFinite]
  · by_cases lower : a 3 < b 3
    all_goals simp [body,Guest.guestFn_u256_lt,progToHOL,expToHOL,shapeToHOL,resultWord,
      evaluateHOLFiniteState_seq,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,evaluateHOLFiniteState_skip,
      evalHOLExact,evalListHOLExact,toExact,aLocal,bLocal,Input.RlpWrite.U256Value.tuple,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,same3,lower,fixClockHOLFinite,shapeOfHOLExact,emptyLocalsHOLFinite]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "u256_lt") = some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 40 (OriginalCodeEnvironment.originalEntry Guest.guestFn_u256_lt) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,U256Eq.formals,Input.RlpWrite.U256Value.tupleShape,Guest.guestFn_u256_lt,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem binary (a b : Quad) : resultWord a b = 0#64 ∨ resultWord a b = 1#64 := by
  classical
  unfold resultWord
  split_ifs <;> simp_all

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (a b : Quad)
    (code : codeFn (ofString "u256_lt") = some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "u256_lt")
      [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b] = some (body,callee,.one) ∧
      callee.lookup (ofString "a") = some (Input.RlpWrite.U256Value.tuple a) ∧ callee.lookup (ofString "b") = some (Input.RlpWrite.U256Value.tuple b) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = ([Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b] : List (ValueHOL 64)).length ∧
      ((formals.zip [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b]).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals,U256Eq.formals,Input.RlpWrite.U256Value.tuple,Input.RlpWrite.U256Value.tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true,
      show ofString "a" ≠ ofString "b" by decide]
  have raw : lookupCodeHOLExact codeFn (ofString "u256_lt") [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b] =
      some (body,U256Eq.rawLocals a b,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [U256Eq.rawLocals,show ofString "a" ≠ ofString "b" by decide]
  · simp [U256Eq.rawLocals]

end InitECandidate.Solver.GasBudget.U256LessThan

#print axioms InitECandidate.Solver.GasBudget.U256LessThan.execute
#print axioms InitECandidate.Solver.GasBudget.U256LessThan.original_code
#print axioms InitECandidate.Solver.GasBudget.U256LessThan.binary

#print axioms InitECandidate.Solver.GasBudget.U256LessThan.environment

namespace InitECandidate.Solver.GasBudget.U256LessThan

/-- The actual limb comparison agrees with the full natural256-bit values. -/
theorem resultWord_one_iff_number_lt (a b : Quad) : resultWord a b=1#64 ↔ U256Zero.number a<U256Zero.number b := by
  have a0:=(a 0).isLt
  have a1:=(a 1).isLt
  have a2:=(a 2).isLt
  have a3:=(a 3).isLt
  have b0:=(b 0).isLt
  have b1:=(b 1).isLt
  have b2:=(b 2).isLt
  have b3:=(b 3).isLt
  have selected : resultWord a b=1#64 ↔
      (if a 3≠b 3 then a 3<b 3 else if a 2≠b 2 then a 2<b 2 else if a 1≠b 1 then a 1<b 1 else a 0<b 0):=by
    unfold resultWord
    split_ifs <;> simp_all
  rw [selected]
  by_cases same3 : a 3=b 3
  · have number3:=congrArg BitVec.toNat same3
    simp only [same3,ne_eq,not_true_eq_false,↓reduceIte]
    by_cases same2 : a 2=b 2
    · have number2:=congrArg BitVec.toNat same2
      simp only [same2,ne_eq,not_true_eq_false,↓reduceIte]
      by_cases same1 : a 1=b 1
      · have number1:=congrArg BitVec.toNat same1
        simp only [same1,ne_eq,not_true_eq_false,↓reduceIte,BitVec.lt_def]
        unfold U256Zero.number
        omega
      · have different : (a 1).toNat≠(b 1).toNat:=fun equal=>same1 (BitVec.eq_of_toNat_eq equal)
        simp only [if_pos same1,BitVec.lt_def]
        unfold U256Zero.number
        omega
    · have different : (a 2).toNat≠(b 2).toNat:=fun equal=>same2 (BitVec.eq_of_toNat_eq equal)
      simp only [if_pos same2,BitVec.lt_def]
      unfold U256Zero.number
      omega
  · have different : (a 3).toNat≠(b 3).toNat:=fun equal=>same3 (BitVec.eq_of_toNat_eq equal)
    simp only [if_pos same3,BitVec.lt_def]
    unfold U256Zero.number
    omega

theorem resultWord_zero_iff_number_le (a b : Quad) : resultWord a b=0#64 ↔ U256Zero.number b≤U256Zero.number a := by
  have one:=resultWord_one_iff_number_lt a b
  have bits:=binary a b
  constructor
  · intro zero
    have notLess : ¬ U256Zero.number a<U256Zero.number b:=by
      intro lower
      have value:=one.mpr lower
      rw [zero] at value
      cases value
    omega
  · intro notLess
    rcases bits with zero|positive
    · exact zero
    · have lower:=one.mp positive
      omega

end InitECandidate.Solver.GasBudget.U256LessThan

#print axioms InitECandidate.Solver.GasBudget.U256LessThan.resultWord_one_iff_number_lt
#print axioms InitECandidate.Solver.GasBudget.U256LessThan.resultWord_zero_iff_number_le
