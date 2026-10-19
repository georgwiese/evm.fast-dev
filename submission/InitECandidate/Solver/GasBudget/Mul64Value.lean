import InitECandidate.Solver.GasBudget.MemoryCostNoException
import InitECandidate.Solver.Input.PureStraight

namespace InitECandidate.Solver.GasBudget.Mul64
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body := ArithmeticEffects.Kind.mul64x64.body
def parts (a b : BitVec 64) : BitVec 64 × BitVec 64 :=
  let a0 := a &&& 4294967295#64
  let a1 := a >>> (32 : Nat)
  let b0 := b &&& 4294967295#64
  let b1 := b >>> (32 : Nat)
  let p00 := a0 * b0
  let p11 := a1 * b1
  let mid := wordAddCarryHOL (a0 * b1) (a1 * b0) 0#64
  let lo := wordAddCarryHOL p00 (mid.1 <<< (32 : Nat)) 0#64
  (lo.1, p11 + ((mid.1 >>> (32 : Nat)) + ((mid.2 <<< (32 : Nat)) + lo.2)))
def value (a b : BitVec 64) : ValueHOL 64 := .rStruct [.val (.word (parts a b).1), .val (.word (parts a b).2)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b") = some (.val (.word b))) :
    ∃ target, evaluateHOLFiniteState source body = (some (.returned (value a b)), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite source := by
  let a0 := a &&& 4294967295#64
  let a1 := a >>> (32 : Nat)
  let b0 := b &&& 4294967295#64
  let b1 := b >>> (32 : Nat)
  let p00 := a0 * b0
  let p11 := a1 * b1
  let mid := wordAddCarryHOL (a0 * b1) (a1 * b0) 0#64
  let lo := wordAddCarryHOL p00 (mid.1 <<< (32 : Nat)) 0#64
  let hi := p11 + ((mid.1 >>> (32 : Nat)) + ((mid.2 <<< (32 : Nat)) + lo.2))
  have aRead : source.locals.lookup (MlString.implode [97#8]) = some (.val (.word a)) := aLocal
  have bRead : source.locals.lookup (MlString.implode [98#8]) = some (.val (.word b)) := bLocal
  change Input.PureStraight.Returns source body (.rStruct [.val (.word lo.1), .val (.word hi)])
  simp only [body, ArithmeticEffects.Kind.body, ArithmeticEffects.Kind.signature, ArithmeticEffects.Kind.original,
    Guest.guestFn_mul64x64, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  refine Input.PureStraight.declares (.val (.word a0)) ?_ (by simp [shapeOfHOLExact, shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval, evalHOLExact, evalListHOLExact, evalListHOLFinite, toExact, ofString, aRead, bRead, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL] <;> rfl
  generalize eq1 : setVarHOLFinite (ofString "a0") (.val (.word a0)) source = s1
  have lookup1 (key : MlS) : s1.locals.lookup key = (if ofString "a0" == key then some (.val (.word a0)) else source.locals.lookup key) := by
    rw [← eq1]
    rfl
  refine Input.PureStraight.declares (.val (.word a1)) ?_ (by simp [shapeOfHOLExact, shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval, evalHOLExact, evalListHOLExact, evalListHOLFinite, toExact, lookup1, ofString, aRead, bRead, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL] <;> rfl
  generalize eq2 : setVarHOLFinite (ofString "a1") (.val (.word a1)) s1 = s2
  have lookup2 (key : MlS) : s2.locals.lookup key = (if ofString "a1" == key then some (.val (.word a1)) else s1.locals.lookup key) := by
    rw [← eq2]
    rfl
  refine Input.PureStraight.declares (.val (.word b0)) ?_ (by simp [shapeOfHOLExact, shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval, evalHOLExact, evalListHOLExact, evalListHOLFinite, toExact, lookup2, lookup1, ofString, aRead, bRead, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL] <;> rfl
  generalize eq3 : setVarHOLFinite (ofString "b0") (.val (.word b0)) s2 = s3
  have lookup3 (key : MlS) : s3.locals.lookup key = (if ofString "b0" == key then some (.val (.word b0)) else s2.locals.lookup key) := by
    rw [← eq3]
    rfl
  refine Input.PureStraight.declares (.val (.word b1)) ?_ (by simp [shapeOfHOLExact, shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval, evalHOLExact, evalListHOLExact, evalListHOLFinite, toExact, lookup3, lookup2, lookup1, ofString, aRead, bRead, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL] <;> rfl
  generalize eq4 : setVarHOLFinite (ofString "b1") (.val (.word b1)) s3 = s4
  have lookup4 (key : MlS) : s4.locals.lookup key = (if ofString "b1" == key then some (.val (.word b1)) else s3.locals.lookup key) := by
    rw [← eq4]
    rfl
  refine Input.PureStraight.declares (.val (.word p00)) ?_ (by simp [shapeOfHOLExact, shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval, evalHOLExact, evalListHOLExact, evalListHOLFinite, toExact, lookup4, lookup3, lookup2, lookup1, ofString, aRead, bRead, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL] <;> rfl
  generalize eq5 : setVarHOLFinite (ofString "p00") (.val (.word p00)) s4 = s5
  have lookup5 (key : MlS) : s5.locals.lookup key = (if ofString "p00" == key then some (.val (.word p00)) else s4.locals.lookup key) := by
    rw [← eq5]
    rfl
  refine Input.PureStraight.declares (.val (.word p11)) ?_ (by simp [shapeOfHOLExact, shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval, evalHOLExact, evalListHOLExact, evalListHOLFinite, toExact, lookup5, lookup4, lookup3, lookup2, lookup1, ofString, aRead, bRead, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL] <;> rfl
  generalize eq6 : setVarHOLFinite (ofString "p11") (.val (.word p11)) s5 = s6
  have lookup6 (key : MlS) : s6.locals.lookup key = (if ofString "p11" == key then some (.val (.word p11)) else s5.locals.lookup key) := by
    rw [← eq6]
    rfl
  refine Input.PureStraight.declares (.rStruct [.val (.word 0#64), .val (.word 0#64)]) ?_ (by simp [shapeOfHOLExact, shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval, evalHOLExact, evalListHOLExact, evalListHOLFinite, toExact, lookup6, lookup5, lookup4, lookup3, lookup2, lookup1, ofString, aRead, bRead, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL] <;> rfl
  generalize eq7 : setVarHOLFinite (ofString "mid") (.rStruct [.val (.word 0#64), .val (.word 0#64)]) s6 = s7
  have lookup7 (key : MlS) : s7.locals.lookup key = (if ofString "mid" == key then some (.rStruct [.val (.word 0#64), .val (.word 0#64)]) else s6.locals.lookup key) := by
    rw [← eq7]
    rfl
  refine Input.PureStraight.carry (a0 * b1) (a1 * b0) 0#64 ?_ ?_ ?_
  · simp [WitnessRadix.QueryBranch.eval, evalHOLExact, evalListHOLExact, evalListHOLFinite, toExact, lookup7, lookup6, lookup5, lookup4, lookup3, lookup2, lookup1, ofString, aRead, bRead, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL] <;> rfl
  · simp [WitnessRadix.QueryBranch.eval, evalHOLExact, evalListHOLExact, evalListHOLFinite, toExact, lookup7, lookup6, lookup5, lookup4, lookup3, lookup2, lookup1, ofString, aRead, bRead, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL] <;> rfl
  generalize eq8 : setVarHOLFinite (ofString "mid") (.rStruct [.val (.word mid.1), .val (.word mid.2)]) s7 = s8
  have lookup8 (key : MlS) : s8.locals.lookup key = (if ofString "mid" == key then some (.rStruct [.val (.word mid.1), .val (.word mid.2)]) else s7.locals.lookup key) := by
    rw [← eq8]
    rfl
  refine Input.PureStraight.declares (.rStruct [.val (.word 0#64), .val (.word 0#64)]) ?_ (by simp [shapeOfHOLExact, shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval, evalHOLExact, evalListHOLExact, evalListHOLFinite, toExact, lookup8, lookup7, lookup6, lookup5, lookup4, lookup3, lookup2, lookup1, ofString, aRead, bRead, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL] <;> rfl
  generalize eq9 : setVarHOLFinite (ofString "lo") (.rStruct [.val (.word 0#64), .val (.word 0#64)]) s8 = s9
  have lookup9 (key : MlS) : s9.locals.lookup key = (if ofString "lo" == key then some (.rStruct [.val (.word 0#64), .val (.word 0#64)]) else s8.locals.lookup key) := by
    rw [← eq9]
    rfl
  refine Input.PureStraight.carry p00 (mid.1 <<< (32 : Nat)) 0#64 ?_ ?_ ?_
  · simp [WitnessRadix.QueryBranch.eval, evalHOLExact, evalListHOLExact, evalListHOLFinite, toExact, lookup9, lookup8, lookup7, lookup6, lookup5, lookup4, lookup3, lookup2, lookup1, ofString, aRead, bRead, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL] <;> rfl
  · simp [WitnessRadix.QueryBranch.eval, evalHOLExact, evalListHOLExact, evalListHOLFinite, toExact, lookup9, lookup8, lookup7, lookup6, lookup5, lookup4, lookup3, lookup2, lookup1, ofString, aRead, bRead, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL] <;> rfl
  generalize eq10 : setVarHOLFinite (ofString "lo") (.rStruct [.val (.word lo.1), .val (.word lo.2)]) s9 = s10
  have lookup10 (key : MlS) : s10.locals.lookup key = (if ofString "lo" == key then some (.rStruct [.val (.word lo.1), .val (.word lo.2)]) else s9.locals.lookup key) := by
    rw [← eq10]
    rfl
  refine Input.PureStraight.declares (.val (.word hi)) ?_ (by simp [shapeOfHOLExact, shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval, evalHOLExact, evalListHOLExact, evalListHOLFinite, toExact, lookup10, lookup9, lookup8, lookup7, lookup6, lookup5, lookup4, lookup3, lookup2, lookup1, ofString, aRead, bRead, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, wordShiftHOL] <;> rfl
  generalize eq11 : setVarHOLFinite (ofString "hi") (.val (.word hi)) s10 = s11
  have lookup11 (key : MlS) : s11.locals.lookup key = (if ofString "hi" == key then some (.val (.word hi)) else s10.locals.lookup key) := by
    rw [← eq11]
    rfl
  refine ⟨emptyLocalsHOLFinite _, ?_, rfl⟩
  simp [evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, toExact, lookup11, lookup10, lookup9, lookup8, lookup7, lookup6, lookup5, lookup4, lookup3, lookup2, lookup1, ofString, aRead, bRead, shapeOfHOLExact, sizeOfShapeWithContextHOL] <;> rfl

theorem zero : value 0#64 0#64 = .rStruct [.val (.word 0#64), .val (.word 0#64)] := by
  simp [value, parts, wordAddCarryHOL]

end InitECandidate.Solver.GasBudget.Mul64

#print axioms InitECandidate.Solver.GasBudget.Mul64.execute
#print axioms InitECandidate.Solver.GasBudget.Mul64.zero
