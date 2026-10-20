import InitECandidate.Solver.Input.PureStraight
import InitECandidate.Solver.GasBudget.U256Eq
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.GasBudget.U256Add
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
abbrev Quad := Input.RlpWrite.U256Value.Words
def body : ProgHOL 64 := match Guest.guestFn_u256_add with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := U256Eq.formals
def r0 (a b : Quad) : BitVec 64 × BitVec 64 := wordAddCarryHOL (a 0) (b 0) 0#64
def r1 (a b : Quad) : BitVec 64 × BitVec 64 := wordAddCarryHOL (a 1) (b 1) (r0 a b).2
def r2 (a b : Quad) : BitVec 64 × BitVec 64 := wordAddCarryHOL (a 2) (b 2) (r1 a b).2
def r3 (a b : Quad) : BitVec 64 × BitVec 64 := wordAddCarryHOL (a 3) (b 3) (r2 a b).2
def result (a b : Quad) : Quad := fun index => match index.val with
  | 0 => (r0 a b).1 | 1 => (r1 a b).1 | 2 => (r2 a b).1 | _ => (r3 a b).1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 600000 in
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : Quad)
    (aLocal : source.locals.lookup (ofString "a") = some (Input.RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b") = some (Input.RlpWrite.U256Value.tuple b)) :
    Input.PureStraight.Returns source body (Input.RlpWrite.U256Value.tuple (result a b)) := by
  classical
  have aRead : source.locals.lookup (MlString.implode [97#8]) = some (Input.RlpWrite.U256Value.tuple a) := aLocal
  have bRead : source.locals.lookup (MlString.implode [98#8]) = some (Input.RlpWrite.U256Value.tuple b) := bLocal
  simp only [body,Guest.guestFn_u256_add,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  refine Input.PureStraight.declares (.rStruct [.val (.word 0#64),.val (.word 0#64)]) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · rfl
  generalize eq1 : setVarHOLFinite (ofString "r0") (.rStruct [.val (.word 0#64),.val (.word 0#64)]) source = s1
  have lookup1 (key : MlS) : s1.locals.lookup key = (if ofString "r0" == key then some (.rStruct [.val (.word 0#64),.val (.word 0#64)]) else source.locals.lookup key) := by rw [← eq1]; rfl
  refine Input.PureStraight.carry (a 0) (b 0) 0#64 ?_ ?_ ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup1] <;> rfl
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup1] <;> rfl
  generalize eq2 : setVarHOLFinite (ofString "r0") (.rStruct [.val (.word (wordAddCarryHOL (a 0) (b 0) 0#64).1),.val (.word (wordAddCarryHOL (a 0) (b 0) 0#64).2)]) s1 = s2
  have lookup2 (key : MlS) : s2.locals.lookup key = (if ofString "r0" == key then some (.rStruct [.val (.word (wordAddCarryHOL (a 0) (b 0) 0#64).1),.val (.word (wordAddCarryHOL (a 0) (b 0) 0#64).2)]) else s1.locals.lookup key) := by rw [← eq2]; rfl
  refine Input.PureStraight.declares (.rStruct [.val (.word 0#64),.val (.word 0#64)]) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · rfl
  generalize eq3 : setVarHOLFinite (ofString "r1") (.rStruct [.val (.word 0#64),.val (.word 0#64)]) s2 = s3
  have lookup3 (key : MlS) : s3.locals.lookup key = (if ofString "r1" == key then some (.rStruct [.val (.word 0#64),.val (.word 0#64)]) else s2.locals.lookup key) := by rw [← eq3]; rfl
  refine Input.PureStraight.carry (a 1) (b 1) (r0 a b).2 ?_ ?_ ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup3,lookup2,lookup1] <;> rfl
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup3,lookup2,lookup1] <;> rfl
  generalize eq4 : setVarHOLFinite (ofString "r1") (.rStruct [.val (.word (wordAddCarryHOL (a 1) (b 1) (r0 a b).2).1),.val (.word (wordAddCarryHOL (a 1) (b 1) (r0 a b).2).2)]) s3 = s4
  have lookup4 (key : MlS) : s4.locals.lookup key = (if ofString "r1" == key then some (.rStruct [.val (.word (wordAddCarryHOL (a 1) (b 1) (r0 a b).2).1),.val (.word (wordAddCarryHOL (a 1) (b 1) (r0 a b).2).2)]) else s3.locals.lookup key) := by rw [← eq4]; rfl
  refine Input.PureStraight.declares (.rStruct [.val (.word 0#64),.val (.word 0#64)]) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · rfl
  generalize eq5 : setVarHOLFinite (ofString "r2") (.rStruct [.val (.word 0#64),.val (.word 0#64)]) s4 = s5
  have lookup5 (key : MlS) : s5.locals.lookup key = (if ofString "r2" == key then some (.rStruct [.val (.word 0#64),.val (.word 0#64)]) else s4.locals.lookup key) := by rw [← eq5]; rfl
  refine Input.PureStraight.carry (a 2) (b 2) (r1 a b).2 ?_ ?_ ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup5,lookup4,lookup3,lookup2,lookup1] <;> rfl
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup5,lookup4,lookup3,lookup2,lookup1] <;> rfl
  generalize eq6 : setVarHOLFinite (ofString "r2") (.rStruct [.val (.word (wordAddCarryHOL (a 2) (b 2) (r1 a b).2).1),.val (.word (wordAddCarryHOL (a 2) (b 2) (r1 a b).2).2)]) s5 = s6
  have lookup6 (key : MlS) : s6.locals.lookup key = (if ofString "r2" == key then some (.rStruct [.val (.word (wordAddCarryHOL (a 2) (b 2) (r1 a b).2).1),.val (.word (wordAddCarryHOL (a 2) (b 2) (r1 a b).2).2)]) else s5.locals.lookup key) := by rw [← eq6]; rfl
  refine Input.PureStraight.declares (.rStruct [.val (.word 0#64),.val (.word 0#64)]) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · rfl
  generalize eq7 : setVarHOLFinite (ofString "r3") (.rStruct [.val (.word 0#64),.val (.word 0#64)]) s6 = s7
  have lookup7 (key : MlS) : s7.locals.lookup key = (if ofString "r3" == key then some (.rStruct [.val (.word 0#64),.val (.word 0#64)]) else s6.locals.lookup key) := by rw [← eq7]; rfl
  refine Input.PureStraight.carry (a 3) (b 3) (r2 a b).2 ?_ ?_ ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1] <;> rfl
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1] <;> rfl
  generalize eq8 : setVarHOLFinite (ofString "r3") (.rStruct [.val (.word (wordAddCarryHOL (a 3) (b 3) (r2 a b).2).1),.val (.word (wordAddCarryHOL (a 3) (b 3) (r2 a b).2).2)]) s7 = s8
  have lookup8 (key : MlS) : s8.locals.lookup key = (if ofString "r3" == key then some (.rStruct [.val (.word (wordAddCarryHOL (a 3) (b 3) (r2 a b).2).1),.val (.word (wordAddCarryHOL (a 3) (b 3) (r2 a b).2).2)]) else s7.locals.lookup key) := by rw [← eq8]; rfl
  refine ⟨emptyLocalsHOLFinite _,?_,rfl⟩
  simp [evaluateHOLFiniteState_return,WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,result,shapeOfHOLExact,sizeOfShapeWithContextHOL] <;> rfl

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "u256_add") = some (formals,body,Input.RlpWrite.U256Value.tupleShape) := by
  have checked := Input.OriginalCode.indexed code installed 50 (OriginalCodeEnvironment.originalEntry Guest.guestFn_u256_add) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,U256Eq.formals,Input.RlpWrite.U256Value.tupleShape,Guest.guestFn_u256_add,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (a b : Quad)
    (code : codeFn (ofString "u256_add") = some (formals,body,Input.RlpWrite.U256Value.tupleShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "u256_add")
      [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b] = some (body,callee,Input.RlpWrite.U256Value.tupleShape) ∧
      callee.lookup (ofString "a") = some (Input.RlpWrite.U256Value.tuple a) ∧ callee.lookup (ofString "b") = some (Input.RlpWrite.U256Value.tuple b) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = ([Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b] : List (ValueHOL 64)).length ∧
      ((formals.zip [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b]).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals,U256Eq.formals,Input.RlpWrite.U256Value.tuple,Input.RlpWrite.U256Value.tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true,
      show ofString "a" ≠ ofString "b" by decide]
  have raw : lookupCodeHOLExact codeFn (ofString "u256_add") [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b] =
      some (body,U256Eq.rawLocals a b,Input.RlpWrite.U256Value.tupleShape) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [U256Eq.rawLocals,show ofString "a" ≠ ofString "b" by decide]
  · simp [U256Eq.rawLocals]

end InitECandidate.Solver.GasBudget.U256Add

#print axioms InitECandidate.Solver.GasBudget.U256Add.execute
#print axioms InitECandidate.Solver.GasBudget.U256Add.original_code
#print axioms InitECandidate.Solver.GasBudget.U256Add.environment

namespace InitECandidate.Solver.GasBudget.U256Sub
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
abbrev Quad := Input.RlpWrite.U256Value.Words
def body : ProgHOL 64 := match Guest.guestFn_u256_sub with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := U256Eq.formals
def r0 (a b : Quad) : BitVec 64 × BitVec 64 := wordAddCarryHOL (a 0) (b 0 ^^^ (0#64 - 1#64)) 1#64
def r1 (a b : Quad) : BitVec 64 × BitVec 64 := wordAddCarryHOL (a 1) (b 1 ^^^ (0#64 - 1#64)) (r0 a b).2
def r2 (a b : Quad) : BitVec 64 × BitVec 64 := wordAddCarryHOL (a 2) (b 2 ^^^ (0#64 - 1#64)) (r1 a b).2
def r3 (a b : Quad) : BitVec 64 × BitVec 64 := wordAddCarryHOL (a 3) (b 3 ^^^ (0#64 - 1#64)) (r2 a b).2
def result (a b : Quad) : Quad := fun index => match index.val with
  | 0 => (r0 a b).1 | 1 => (r1 a b).1 | 2 => (r2 a b).1 | _ => (r3 a b).1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 600000 in
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : Quad)
    (aLocal : source.locals.lookup (ofString "a") = some (Input.RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b") = some (Input.RlpWrite.U256Value.tuple b)) :
    Input.PureStraight.Returns source body (Input.RlpWrite.U256Value.tuple (result a b)) := by
  classical
  have aRead : source.locals.lookup (MlString.implode [97#8]) = some (Input.RlpWrite.U256Value.tuple a) := aLocal
  have bRead : source.locals.lookup (MlString.implode [98#8]) = some (Input.RlpWrite.U256Value.tuple b) := bLocal
  simp only [body,Guest.guestFn_u256_sub,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  refine Input.PureStraight.declares (.rStruct [.val (.word 0#64),.val (.word 0#64)]) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · rfl
  generalize eq1 : setVarHOLFinite (ofString "r0") (.rStruct [.val (.word 0#64),.val (.word 0#64)]) source = s1
  have lookup1 (key : MlS) : s1.locals.lookup key = (if ofString "r0" == key then some (.rStruct [.val (.word 0#64),.val (.word 0#64)]) else source.locals.lookup key) := by rw [← eq1]; rfl
  refine Input.PureStraight.carry (a 0) (b 0 ^^^ (0#64 - 1#64)) 1#64 ?_ ?_ ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup1] <;> rfl
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup1] <;> rfl
  generalize eq2 : setVarHOLFinite (ofString "r0") (.rStruct [.val (.word (wordAddCarryHOL (a 0) (b 0 ^^^ (0#64 - 1#64)) 1#64).1),.val (.word (wordAddCarryHOL (a 0) (b 0 ^^^ (0#64 - 1#64)) 1#64).2)]) s1 = s2
  have lookup2 (key : MlS) : s2.locals.lookup key = (if ofString "r0" == key then some (.rStruct [.val (.word (wordAddCarryHOL (a 0) (b 0 ^^^ (0#64 - 1#64)) 1#64).1),.val (.word (wordAddCarryHOL (a 0) (b 0 ^^^ (0#64 - 1#64)) 1#64).2)]) else s1.locals.lookup key) := by rw [← eq2]; rfl
  refine Input.PureStraight.declares (.rStruct [.val (.word 0#64),.val (.word 0#64)]) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · rfl
  generalize eq3 : setVarHOLFinite (ofString "r1") (.rStruct [.val (.word 0#64),.val (.word 0#64)]) s2 = s3
  have lookup3 (key : MlS) : s3.locals.lookup key = (if ofString "r1" == key then some (.rStruct [.val (.word 0#64),.val (.word 0#64)]) else s2.locals.lookup key) := by rw [← eq3]; rfl
  refine Input.PureStraight.carry (a 1) (b 1 ^^^ (0#64 - 1#64)) (r0 a b).2 ?_ ?_ ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup3,lookup2,lookup1] <;> rfl
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup3,lookup2,lookup1] <;> rfl
  generalize eq4 : setVarHOLFinite (ofString "r1") (.rStruct [.val (.word (wordAddCarryHOL (a 1) (b 1 ^^^ (0#64 - 1#64)) (r0 a b).2).1),.val (.word (wordAddCarryHOL (a 1) (b 1 ^^^ (0#64 - 1#64)) (r0 a b).2).2)]) s3 = s4
  have lookup4 (key : MlS) : s4.locals.lookup key = (if ofString "r1" == key then some (.rStruct [.val (.word (wordAddCarryHOL (a 1) (b 1 ^^^ (0#64 - 1#64)) (r0 a b).2).1),.val (.word (wordAddCarryHOL (a 1) (b 1 ^^^ (0#64 - 1#64)) (r0 a b).2).2)]) else s3.locals.lookup key) := by rw [← eq4]; rfl
  refine Input.PureStraight.declares (.rStruct [.val (.word 0#64),.val (.word 0#64)]) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · rfl
  generalize eq5 : setVarHOLFinite (ofString "r2") (.rStruct [.val (.word 0#64),.val (.word 0#64)]) s4 = s5
  have lookup5 (key : MlS) : s5.locals.lookup key = (if ofString "r2" == key then some (.rStruct [.val (.word 0#64),.val (.word 0#64)]) else s4.locals.lookup key) := by rw [← eq5]; rfl
  refine Input.PureStraight.carry (a 2) (b 2 ^^^ (0#64 - 1#64)) (r1 a b).2 ?_ ?_ ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup5,lookup4,lookup3,lookup2,lookup1] <;> rfl
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup5,lookup4,lookup3,lookup2,lookup1] <;> rfl
  generalize eq6 : setVarHOLFinite (ofString "r2") (.rStruct [.val (.word (wordAddCarryHOL (a 2) (b 2 ^^^ (0#64 - 1#64)) (r1 a b).2).1),.val (.word (wordAddCarryHOL (a 2) (b 2 ^^^ (0#64 - 1#64)) (r1 a b).2).2)]) s5 = s6
  have lookup6 (key : MlS) : s6.locals.lookup key = (if ofString "r2" == key then some (.rStruct [.val (.word (wordAddCarryHOL (a 2) (b 2 ^^^ (0#64 - 1#64)) (r1 a b).2).1),.val (.word (wordAddCarryHOL (a 2) (b 2 ^^^ (0#64 - 1#64)) (r1 a b).2).2)]) else s5.locals.lookup key) := by rw [← eq6]; rfl
  refine Input.PureStraight.declares (.rStruct [.val (.word 0#64),.val (.word 0#64)]) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · rfl
  generalize eq7 : setVarHOLFinite (ofString "r3") (.rStruct [.val (.word 0#64),.val (.word 0#64)]) s6 = s7
  have lookup7 (key : MlS) : s7.locals.lookup key = (if ofString "r3" == key then some (.rStruct [.val (.word 0#64),.val (.word 0#64)]) else s6.locals.lookup key) := by rw [← eq7]; rfl
  refine Input.PureStraight.carry (a 3) (b 3 ^^^ (0#64 - 1#64)) (r2 a b).2 ?_ ?_ ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1] <;> rfl
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1] <;> rfl
  generalize eq8 : setVarHOLFinite (ofString "r3") (.rStruct [.val (.word (wordAddCarryHOL (a 3) (b 3 ^^^ (0#64 - 1#64)) (r2 a b).2).1),.val (.word (wordAddCarryHOL (a 3) (b 3 ^^^ (0#64 - 1#64)) (r2 a b).2).2)]) s7 = s8
  have lookup8 (key : MlS) : s8.locals.lookup key = (if ofString "r3" == key then some (.rStruct [.val (.word (wordAddCarryHOL (a 3) (b 3 ^^^ (0#64 - 1#64)) (r2 a b).2).1),.val (.word (wordAddCarryHOL (a 3) (b 3 ^^^ (0#64 - 1#64)) (r2 a b).2).2)]) else s7.locals.lookup key) := by rw [← eq8]; rfl
  refine ⟨emptyLocalsHOLFinite _,?_,rfl⟩
  simp [evaluateHOLFiniteState_return,WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,aRead,bRead,Input.RlpWrite.U256Value.tuple,localVar,valueIsWord,valueWord,wordOpHOL,wordOp,r0,r1,r2,r3,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,result,shapeOfHOLExact,sizeOfShapeWithContextHOL] <;> rfl

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "u256_sub") = some (formals,body,Input.RlpWrite.U256Value.tupleShape) := by
  have checked := Input.OriginalCode.indexed code installed 51 (OriginalCodeEnvironment.originalEntry Guest.guestFn_u256_sub) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,U256Eq.formals,Input.RlpWrite.U256Value.tupleShape,Guest.guestFn_u256_sub,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (a b : Quad)
    (code : codeFn (ofString "u256_sub") = some (formals,body,Input.RlpWrite.U256Value.tupleShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "u256_sub")
      [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b] = some (body,callee,Input.RlpWrite.U256Value.tupleShape) ∧
      callee.lookup (ofString "a") = some (Input.RlpWrite.U256Value.tuple a) ∧ callee.lookup (ofString "b") = some (Input.RlpWrite.U256Value.tuple b) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = ([Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b] : List (ValueHOL 64)).length ∧
      ((formals.zip [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b]).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals,U256Eq.formals,Input.RlpWrite.U256Value.tuple,Input.RlpWrite.U256Value.tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true,
      show ofString "a" ≠ ofString "b" by decide]
  have raw : lookupCodeHOLExact codeFn (ofString "u256_sub") [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b] =
      some (body,U256Eq.rawLocals a b,Input.RlpWrite.U256Value.tupleShape) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [U256Eq.rawLocals,show ofString "a" ≠ ofString "b" by decide]
  · simp [U256Eq.rawLocals]

end InitECandidate.Solver.GasBudget.U256Sub

#print axioms InitECandidate.Solver.GasBudget.U256Sub.execute
#print axioms InitECandidate.Solver.GasBudget.U256Sub.original_code
#print axioms InitECandidate.Solver.GasBudget.U256Sub.environment
