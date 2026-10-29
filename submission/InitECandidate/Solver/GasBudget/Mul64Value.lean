import Mathlib.Tactic.Ring
import InitECandidate.Solver.GasBudget.ArithmeticClockPrice
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


namespace InitECandidate.Solver.GasBudget.Mul64
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual current two-word multiply signature for the existing checked
value execution; no unrelated dispatch/memory-cost proof root is imported. -/
theorem current_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "mul64x64")=some ([(ofString "a",.one),(ofString "b",.one)],body,.comb [.one,.one]) := by
  have known:=ArithmeticEffects.current_environment code installed .mul64x64
  simpa only [ArithmeticEffects.Kind.name,ArithmeticEffects.Kind.signature,ArithmeticEffects.Kind.original,ArithmeticEffects.Kind.body,
    body,Guest.guestFn_mul64x64,shapeToHOL,List.map_cons,List.map_nil] using known

end InitECandidate.Solver.GasBudget.Mul64

#print axioms InitECandidate.Solver.GasBudget.Mul64.current_code

namespace InitECandidate.Solver.GasBudget.Mul64
open Flapjack

/-- Exact natural interpretation of the source primitive used by the real
mul64x64 and wide multipliers, including the overflow word. -/
theorem carry_number (left right : BitVec 64) :
    (wordAddCarryHOL left right 0#64).1.toNat+2^64*(wordAddCarryHOL left right 0#64).2.toNat=left.toNat+right.toNat := by
  have leftBound:=left.isLt
  have rightBound:=right.isLt
  change (left.toNat+right.toNat)%2^64+2^64*(if 2^64≤left.toNat+right.toNat then 1#64 else 0#64).toNat=left.toNat+right.toNat
  by_cases overflow : 2^64≤left.toNat+right.toNat
  · rw [if_pos overflow]
    change (left.toNat+right.toNat)%2^64+2^64=left.toNat+right.toNat
    omega
  · rw [if_neg overflow]
    change (left.toNat+right.toNat)%2^64=left.toNat+right.toNat
    omega

theorem carry_low_number (left right : BitVec 64) :
    (wordAddCarryHOL left right 0#64).1.toNat=(left.toNat+right.toNat)%2^64 := by
  simp [wordAddCarryHOL]

theorem carry_high_number (left right : BitVec 64) :
    (wordAddCarryHOL left right 0#64).2.toNat=(left.toNat+right.toNat)/2^64 := by
  have full:=carry_number left right
  have split:=Nat.mod_add_div (left.toNat+right.toNat) (2^64)
  rw [carry_low_number] at full
  omega

theorem low_half_number (word : BitVec 64) : (word &&& 4294967295#64).toNat=word.toNat%2^32 := by
  rw [BitVec.toNat_and]
  change word.toNat &&& (2^32-1)=word.toNat%2^32
  exact Nat.and_two_pow_sub_one_eq_mod word.toNat 32

theorem high_half_number (word : BitVec 64) : (word>>>(32:Nat)).toNat=word.toNat/2^32 := by
  rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

theorem halves_number (word : BitVec 64) :
    (word &&& 4294967295#64).toNat+2^32*(word>>>(32:Nat)).toNat=word.toNat := by
  rw [low_half_number,high_half_number]
  exact Nat.mod_add_div word.toNat (2^32)

end InitECandidate.Solver.GasBudget.Mul64

#print axioms InitECandidate.Solver.GasBudget.Mul64.carry_number
#print axioms InitECandidate.Solver.GasBudget.Mul64.carry_low_number
#print axioms InitECandidate.Solver.GasBudget.Mul64.carry_high_number
#print axioms InitECandidate.Solver.GasBudget.Mul64.low_half_number
#print axioms InitECandidate.Solver.GasBudget.Mul64.high_half_number
#print axioms InitECandidate.Solver.GasBudget.Mul64.halves_number

namespace InitECandidate.Solver.GasBudget.Mul64
open Flapjack

theorem low_half_lt (word : BitVec 64) : (word &&& 4294967295#64).toNat<2^32 := by
  rw [low_half_number]
  exact Nat.mod_lt _ (by decide)

theorem high_half_lt (word : BitVec 64) : (word>>>(32:Nat)).toNat<2^32 := by
  rw [high_half_number]
  have bound:=word.isLt
  omega

theorem small_product_number (left right : BitVec 64) (leftBound : left.toNat<2^32) (rightBound : right.toNat<2^32) :
    (left*right).toNat=left.toNat*right.toNat := by
  have bounded : left.toNat*right.toNat<2^64:=by
    calc
      left.toNat*right.toNat≤(2^32-1)*(2^32-1):=Nat.mul_le_mul (by omega) (by omega)
      _<2^64:=by decide
  rw [BitVec.toNat_mul,Nat.mod_eq_of_lt bounded]

theorem shift_half_number (word : BitVec 64) :
    (word<<<(32:Nat)).toNat=(word.toNat%2^32)*2^32 := by
  rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  rw [show (2:Nat)^64=2^32*2^32 from Nat.pow_add 2 32 32]
  exact Nat.mul_mod_mul_right (2^32) word.toNat (2^32)

theorem shift_flag_number (word : BitVec 64) (small : word.toNat≤1) :
    (word<<<(32:Nat)).toNat=word.toNat*2^32 := by
  rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The actual schoolbook half-word multiplication returns the exact full
128-bit natural product, including its three source carry computations. -/
theorem parts_product (a b : BitVec 64) :
    (parts a b).1.toNat+2^64*(parts a b).2.toNat=a.toNat*b.toNat := by
  let base : Nat:=2^32
  let modulus : Nat:=2^64
  let a0:=a &&& 4294967295#64
  let a1:=a>>>(32:Nat)
  let b0:=b &&& 4294967295#64
  let b1:=b>>>(32:Nat)
  let p00:=a0*b0
  let p01:=a0*b1
  let p10:=a1*b0
  let p11:=a1*b1
  let mid:=wordAddCarryHOL p01 p10 0#64
  let lo:=wordAddCarryHOL p00 (mid.1<<<(32:Nat)) 0#64
  let high:=p11.toNat+((mid.1>>>(32:Nat)).toNat+((mid.2<<<(32:Nat)).toNat+lo.2.toNat))
  have aSplit : a0.toNat+base*a1.toNat=a.toNat:=halves_number a
  have bSplit : b0.toNat+base*b1.toNat=b.toNat:=halves_number b
  have p00Number : p00.toNat=a0.toNat*b0.toNat:=small_product_number a0 b0 (low_half_lt a) (low_half_lt b)
  have p01Number : p01.toNat=a0.toNat*b1.toNat:=small_product_number a0 b1 (low_half_lt a) (high_half_lt b)
  have p10Number : p10.toNat=a1.toNat*b0.toNat:=small_product_number a1 b0 (high_half_lt a) (low_half_lt b)
  have p11Number : p11.toNat=a1.toNat*b1.toNat:=small_product_number a1 b1 (high_half_lt a) (high_half_lt b)
  have expanded : a.toNat*b.toNat=p00.toNat+base*(p01.toNat+p10.toNat)+modulus*p11.toNat:=by
    rw [←aSplit,←bSplit,p00Number,p01Number,p10Number,p11Number]
    dsimp only [base,modulus]
    ring
  have midCarry : mid.1.toNat+modulus*mid.2.toNat=p01.toNat+p10.toNat:=carry_number p01 p10
  have midSplit : mid.1.toNat%base+base*(mid.1>>>(32:Nat)).toNat=mid.1.toNat:=by
    rw [high_half_number]
    exact Nat.mod_add_div mid.1.toNat base
  have lowShift : (mid.1<<<(32:Nat)).toNat=(mid.1.toNat%base)*base:=shift_half_number mid.1
  have midFlag : mid.2.toNat≤1:=by
    change (wordAddCarryHOL p01 p10 0#64).2.toNat≤1
    rw [carry_high_number]
    have first:=p01.isLt
    have second:=p10.isLt
    omega
  have highShift : (mid.2<<<(32:Nat)).toNat=mid.2.toNat*base:=shift_flag_number mid.2 midFlag
  have lowCarry : lo.1.toNat+modulus*lo.2.toNat=p00.toNat+(mid.1.toNat%base)*base:=by
    have carry:=carry_number p00 (mid.1<<<(32:Nat))
    rw [lowShift] at carry
    exact carry
  have packed : lo.1.toNat+modulus*high=a.toNat*b.toNat:=by
    rw [expanded]
    have weightedMid:=congrArg (fun value : Nat=>base*value) midCarry
    have weightedSplit:=congrArg (fun value : Nat=>base*value) midSplit
    dsimp only [high]
    rw [highShift]
    dsimp only [base,modulus] at *
    omega
  have productBound : a.toNat*b.toNat<modulus*modulus:=by
    have first:=a.isLt
    have second:=b.isLt
    calc
      a.toNat*b.toNat≤(modulus-1)*(modulus-1):=Nat.mul_le_mul (by dsimp only [modulus]; omega) (by dsimp only [modulus]; omega)
      _<modulus*modulus:=by norm_num [modulus] <;> omega
  have highBound : high<modulus:=by
    dsimp only [modulus] at *
    omega
  have represented : (parts a b).2=BitVec.ofNat 64 high:=by
    change p11+((mid.1>>>(32:Nat))+((mid.2<<<(32:Nat))+lo.2))=BitVec.ofNat 64 high
    dsimp only [high]
    simp only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have highNumber : (parts a b).2.toNat=high:=by
    rw [represented,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt highBound
  rw [highNumber]
  exact packed

end InitECandidate.Solver.GasBudget.Mul64

#print axioms InitECandidate.Solver.GasBudget.Mul64.low_half_lt
#print axioms InitECandidate.Solver.GasBudget.Mul64.high_half_lt
#print axioms InitECandidate.Solver.GasBudget.Mul64.small_product_number
#print axioms InitECandidate.Solver.GasBudget.Mul64.parts_product

#print axioms InitECandidate.Solver.GasBudget.Mul64.shift_half_number
#print axioms InitECandidate.Solver.GasBudget.Mul64.shift_flag_number


namespace InitECandidate.Solver.GasBudget.Mul64
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The same actual current software body returns limbs representing the
full natural product and retains every physical field and its source clock. -/
theorem execute_product (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b")=some (.val (.word b))) :
    ∃ target low high,evaluateHOLFiniteState source body=(some (.returned (.rStruct [.val (.word low),.val (.word high)])),target) ∧
      low.toNat+2^64*high.toNat=a.toNat*b.toNat ∧ emptyLocalsHOLFinite target=emptyLocalsHOLFinite source := by
  obtain ⟨target,run,frame⟩:=execute source a b installed aLocal bLocal
  exact ⟨target,(parts a b).1,(parts a b).2,run,parts_product a b,frame⟩

end InitECandidate.Solver.GasBudget.Mul64

#print axioms InitECandidate.Solver.GasBudget.Mul64.execute_product
