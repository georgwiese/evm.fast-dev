import Mathlib.Tactic.Ring
import InitECandidate.Solver.Input.ScopedCallNormal
import InitECandidate.Solver.GasBudget.U256Zero
import InitECandidate.Solver.Input.CallResume
import InitECandidate.Solver.Input.WordTupleFour
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


namespace InitECandidate.Solver.GasBudget.Mul64
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (a b : BitVec 64)
    (code : codeFn (ofString "mul64x64")=some ([(ofString "a",.one),(ofString "b",.one)],body,.comb [.one,.one])) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "mul64x64") [.val (.word a),.val (.word b)]=some (body,callee,.comb [.one,.one]) ∧
      callee.lookup (ofString "a")=some (.val (.word a)) ∧ callee.lookup (ofString "b")=some (.val (.word b)) := by
  let locals : MlS→Option (ValueHOL 64):=fun name=>
    if name=ofString "b" then some (.val (.word b)) else if name=ofString "a" then some (.val (.word a)) else none
  have valid : (([(ofString "a",.one),(ofString "b",.one)] : List (MlS×ShapeHOL)).map Prod.fst).Nodup ∧
      ([(ofString "a",.one),(ofString "b",.one)] : List (MlS×ShapeHOL)).length=([.val (.word a),.val (.word b)] : List (ValueHOL 64)).length ∧
      ((([(ofString "a",.one),(ofString "b",.one)] : List (MlS×ShapeHOL)).zip [.val (.word a),.val (.word b)]).all
        (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [shapeOfHOLExact,shapeEqHOL_eq_true,show ofString "a"≠ofString "b" by decide]
  have raw : lookupCodeHOLExact codeFn (ofString "mul64x64") [.val (.word a),.val (.word b)]=some (body,locals,.comb [.one,.one]) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,bindings⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [bindings]
  · simp [locals,show ofString "a"≠ofString "b" by decide]
  · simp [locals]

/-- The real scalar call returns its two-word product and resumes its real
continuation with exactly one source tick spent. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (installed : Input.OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word a),.val (.word b)]) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) (.comb [.one,.one]) (ofString "mul64x64") arguments continuation)=
      (let output:=evaluateHOLFiniteState (setVarHOLFinite (ofString name) (value a b) {source with clock:=source.clock-1}) continuation
      (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,aLocal,bLocal⟩:=environment source.code.lookup a b (current_code source.code installed)
  obtain ⟨target,run,frame⟩:=execute (callEntryStateHOLFinite source callee) a b installed aLocal bLocal
  have actual:=Input.CallNormal.return_execute source target name (.comb [.one,.one]) (ofString "mul64x64") arguments _
    body continuation callee (.comb [.one,.one]) (value a b) args called enough run
    (by simp [value,shapeOfHOLExact,shapeEqHOL_eq_true])
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  have entry : Input.CallNormal.continuationEntry source target name (value a b)=
      setVarHOLFinite (ofString name) (value a b) {source with clock:=source.clock-1} := by
    change setVarHOLFinite _ _ {target with locals:=source.locals}=_
    exact congrArg (setVarHOLFinite (ofString name) (value a b)) callerFrame
  rw [entry] at actual
  exact actual

end InitECandidate.Solver.GasBudget.Mul64

#print axioms InitECandidate.Solver.GasBudget.Mul64.environment
#print axioms InitECandidate.Solver.GasBudget.Mul64.call_execute

namespace InitECandidate.Solver.GasBudget.U256Multiply
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=ArithmeticEffects.Kind.u256_mul.body
def wordQuad (word : BitVec 64) : Input.RlpWrite.U256Value.Words:=fun index=>if index.val=0 then word else 0#64
def productQuad (a b : BitVec 64) : Input.RlpWrite.U256Value.Words:=fun index=>
  if index.val=0 then (Mul64.parts a b).1 else if index.val=1 then (Mul64.parts a b).2 else 0#64

def fastGuard : ExpHOL 64:=.cmp .equal (.op .or [.rfield 1 (localVar "a"),.rfield 2 (localVar "a"),.rfield 3 (localVar "a"),
  .rfield 1 (localVar "b"),.rfield 2 (localVar "b"),.rfield 3 (localVar "b")]) (.const 0#64)
def fastArguments : List (ExpHOL 64):=[.rfield 0 (localVar "a"),.rfield 0 (localVar "b")]
def fastReturn : ProgHOL 64:=.return (.rstruct [.rfield 0 (localVar "p"),.rfield 1 (localVar "p"),.const 0#64,.const 0#64])
def fastCall : ProgHOL 64:=.decCall (ofString "p") (.comb [.one,.one]) (ofString "mul64x64") fastArguments fastReturn
def slowBody : ProgHOL 64:=match body with | .seq _ rest=>rest | _=>.skip

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem shape : body=.seq (.ite fastGuard fastCall .skip) slowBody := by
  simp only [body,slowBody,fastGuard,fastCall,fastArguments,fastReturn,ArithmeticEffects.Kind.body,ArithmeticEffects.Kind.signature,
    ArithmeticEffects.Kind.original,Guest.guestFn_u256_mul,progToHOL,expToHOL,shapeToHOL,localVar,List.map_cons,List.map_nil,Option.map_none]

theorem word_guard (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (aLocal : source.locals.lookup (ofString "a")=some (Input.RlpWrite.U256Value.tuple (wordQuad a)))
    (bLocal : source.locals.lookup (ofString "b")=some (Input.RlpWrite.U256Value.tuple (wordQuad b))) :
    eval source fastGuard=some (.val (.word 1#64)) := by
  simp [eval,fastGuard,evalHOLExact,evalListHOLExact,toExact,localVar,aLocal,bLocal,Input.RlpWrite.U256Value.tuple,wordQuad,
    valueIsWord,valueWord,wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rfl

theorem word_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (aLocal : source.locals.lookup (ofString "a")=some (Input.RlpWrite.U256Value.tuple (wordQuad a)))
    (bLocal : source.locals.lookup (ofString "b")=some (Input.RlpWrite.U256Value.tuple (wordQuad b))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) fastArguments=
      some [.val (.word a),.val (.word b)] := by
  simp [fastArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,aLocal,bLocal,Input.RlpWrite.U256Value.tuple,wordQuad]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The original fast branch multiplies two one-word inputs into the exact
128-bit product in the real four-limb result. -/
theorem word_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (Input.RlpWrite.U256Value.tuple (wordQuad a)))
    (bLocal : source.locals.lookup (ofString "b")=some (Input.RlpWrite.U256Value.tuple (wordQuad b)))
    (enough : 1≤source.clock) :
    ∃ target,evaluateHOLFiniteState source body=(some (.returned (Input.RlpWrite.U256Value.tuple (productQuad a b))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1} := by
  classical
  have guard:=word_guard source a b aLocal bLocal
  have args:=word_arguments source a b aLocal bLocal
  let next:=setVarHOLFinite (ofString "p") (Mul64.value a b) {source with clock:=source.clock-1}
  have returned : evaluateHOLFiniteState next fastReturn=
      (some (.returned (Input.RlpWrite.U256Value.tuple (productQuad a b))),emptyLocalsHOLFinite next):=by
    change evaluateHOLFiniteState next fastReturn=
      (some (.returned (.rStruct [.val (.word (Mul64.parts a b).1),.val (.word (Mul64.parts a b).2),.val (.word 0#64),.val (.word 0#64)])),emptyLocalsHOLFinite next)
    simp [next,fastReturn,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,
      setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Mul64.value,Input.RlpWrite.U256Value.tuple,productQuad,
      shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have called:=Mul64.call_execute source a b "p" fastArguments fastReturn installed args enough
  change evaluateHOLFiniteState source fastCall=_ at called
  change evaluateHOLFiniteState source fastCall=
    (let output:=evaluateHOLFiniteState next fastReturn;(output.1,restore source "p" output.2)) at called
  rw [returned] at called
  have branch : evaluateHOLFiniteState source (.ite fastGuard fastCall .skip)=
      (some (.returned (Input.RlpWrite.U256Value.tuple (productQuad a b))),restore source "p" (emptyLocalsHOLFinite next)):=by
    rw [evaluateHOLFiniteState_ite]
    change evalHOLExact source.toExact fastGuard=_ at guard
    rw [guard]
    exact called
  refine ⟨restore source "p" (emptyLocalsHOLFinite next),?_,rfl⟩
  rw [shape]
  exact WitnessRadix.StateSteps.stopped_sequence source _ _ _ _ branch (by change source.clock-1≤source.clock;omega)

theorem word_product (a b : BitVec 64) :
    (productQuad a b 0).toNat+2^64*(productQuad a b 1).toNat+2^128*(productQuad a b 2).toNat+2^192*(productQuad a b 3).toNat=
      a.toNat*b.toNat := by
  change (Mul64.parts a b).1.toNat+2^64*(Mul64.parts a b).2.toNat+2^128*0+2^192*0=a.toNat*b.toNat
  simpa only [Nat.mul_zero,Nat.add_zero] using Mul64.parts_product a b

end InitECandidate.Solver.GasBudget.U256Multiply

#print axioms InitECandidate.Solver.GasBudget.U256Multiply.shape
#print axioms InitECandidate.Solver.GasBudget.U256Multiply.word_execute
#print axioms InitECandidate.Solver.GasBudget.U256Multiply.word_product


namespace InitECandidate.Solver.GasBudget.U256Multiply
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem current_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "u256_mul")=some ([(ofString "a",Input.RlpWrite.U256Value.tupleShape),
      (ofString "b",Input.RlpWrite.U256Value.tupleShape)],body,Input.RlpWrite.U256Value.tupleShape) := by
  have known:=ArithmeticEffects.current_environment code installed .u256_mul
  simpa only [ArithmeticEffects.Kind.name,ArithmeticEffects.Kind.signature,ArithmeticEffects.Kind.original,
    body,ArithmeticEffects.Kind.body,Input.RlpWrite.U256Value.tupleShape,Guest.guestFn_u256_mul,shapeToHOL,List.map_cons,List.map_nil] using known

/-- Includes the actual zero-clock outcome; one-word multiplication spends
at most one body source tick and never needs a division workspace. -/
theorem word_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (Input.RlpWrite.U256Value.tuple (wordQuad a)))
    (bLocal : source.locals.lookup (ofString "b")=some (Input.RlpWrite.U256Value.tuple (wordQuad b))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤1 := by
  by_cases enough : 1≤source.clock
  · obtain ⟨target,run,frame⟩:=word_execute source a b installed aLocal bLocal enough
    have clock:=congrArg PanSemStateFiniteExact.clock frame
    change target.clock=source.clock-1 at clock
    rw [run]
    simp only [clock]
    omega
  · omega

/-- Every actual normal result derives the clock funding and the concrete
product; neither is an assumption about a future helper return. -/
theorem word_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (Input.RlpWrite.U256Value.tuple (wordQuad a)))
    (bLocal : source.locals.lookup (ofString "b")=some (Input.RlpWrite.U256Value.tuple (wordQuad b)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    1≤source.clock ∧ value=Input.RlpWrite.U256Value.tuple (productQuad a b) ∧
      emptyLocalsHOLFinite post=emptyLocalsHOLFinite {source with clock:=source.clock-1} := by
  classical
  have enough : 1≤source.clock:=by
    by_contra short
    have zero : source.clock=0:=by omega
    have guard:=word_guard source a b aLocal bLocal
    change evalHOLExact source.toExact fastGuard=_ at guard
    have args:=word_arguments source a b aLocal bLocal
    obtain ⟨callee,called,aCell,bCell⟩:=Mul64.environment source.code.lookup a b (Mul64.current_code source.code installed)
    rw [shape,evaluateHOLFiniteState_seq,evaluateHOLFiniteState_ite,guard] at normal
    simp only [show (1#64 : BitVec 64)≠0#64 by decide,↓reduceIte] at normal
    rw [fastCall,evaluateHOLFiniteState_decCall_fixClockRewrite] at normal
    simp only [args,called,if_pos zero] at normal
    simp [fixClockHOLFinite,zero] at normal
  obtain ⟨target,run,frame⟩:=word_execute source a b installed aLocal bLocal enough
  have same:=normal.symm.trans run
  have valueEq : value=Input.RlpWrite.U256Value.tuple (productQuad a b):=by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using congrArg Prod.fst same
  have postEq : post=target:=congrArg Prod.snd same
  exact ⟨enough,valueEq,postEq ▸ frame⟩

def fromWordBody : ProgHOL 64:=ArithmeticEffects.Kind.u256_from_word.body

theorem from_word_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "u256_from_word")=some ([(ofString "w",.one)],fromWordBody,Input.RlpWrite.U256Value.tupleShape) := by
  have known:=ArithmeticEffects.current_environment code installed .u256_from_word
  simpa only [ArithmeticEffects.Kind.name,ArithmeticEffects.Kind.signature,ArithmeticEffects.Kind.original,
    fromWordBody,ArithmeticEffects.Kind.body,Input.RlpWrite.U256Value.tupleShape,Guest.guestFn_u256_from_word,shapeToHOL,List.map_cons,List.map_nil] using known

theorem from_word_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (wordLocal : source.locals.lookup (ofString "w")=some (.val (.word word))) :
    evaluateHOLFiniteState source fromWordBody=(some (.returned (Input.RlpWrite.U256Value.tuple (wordQuad word))),emptyLocalsHOLFinite source) := by
  change evaluateHOLFiniteState source fromWordBody=
    (some (.returned (.rStruct [.val (.word word),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)])),emptyLocalsHOLFinite source)
  simp [fromWordBody,ArithmeticEffects.Kind.body,ArithmeticEffects.Kind.signature,ArithmeticEffects.Kind.original,
    Guest.guestFn_u256_from_word,progToHOL,expToHOL,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,
    wordLocal,shapeOfHOLExact,sizeOfShapeWithContextHOL]

end InitECandidate.Solver.GasBudget.U256Multiply

#print axioms InitECandidate.Solver.GasBudget.U256Multiply.word_guard
#print axioms InitECandidate.Solver.GasBudget.U256Multiply.word_arguments
#print axioms InitECandidate.Solver.GasBudget.U256Multiply.current_code
#print axioms InitECandidate.Solver.GasBudget.U256Multiply.word_cost
#print axioms InitECandidate.Solver.GasBudget.U256Multiply.word_normal
#print axioms InitECandidate.Solver.GasBudget.U256Multiply.from_word_code
#print axioms InitECandidate.Solver.GasBudget.U256Multiply.from_word_execute


namespace InitECandidate.Solver.GasBudget.U256Multiply
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def fullBody : ProgHOL 64:=ArithmeticEffects.Kind.u256_mul_full.body
private def dropProductCalls : Nat→ProgHOL 64→ProgHOL 64
  | 0,program=>program
  | count+1,.decCall _ _ _ _ rest=>dropProductCalls count rest
  | _+1,_=>.skip
def afterProducts : ProgHOL 64:=dropProductCalls 16 fullBody

def scalarFirst (a : Input.RlpWrite.U256Value.Words) (b : BitVec 64) : BitVec 64×BitVec 64:=
  wordAddCarryHOL (Mul64.parts (a 0) b).2 (Mul64.parts (a 1) b).1 0#64
def scalarSecondHigh (a : Input.RlpWrite.U256Value.Words) (b : BitVec 64) : BitVec 64×BitVec 64:=
  wordAddCarryHOL (scalarFirst a b).2 (Mul64.parts (a 1) b).2 0#64
def scalarSecond (a : Input.RlpWrite.U256Value.Words) (b : BitVec 64) : BitVec 64×BitVec 64:=
  wordAddCarryHOL (scalarSecondHigh a b).1 (Mul64.parts (a 2) b).1 0#64
def scalarThirdHigh (a : Input.RlpWrite.U256Value.Words) (b : BitVec 64) : BitVec 64×BitVec 64:=
  wordAddCarryHOL ((scalarSecondHigh a b).2+(scalarSecond a b).2) (Mul64.parts (a 2) b).2 0#64
def scalarThird (a : Input.RlpWrite.U256Value.Words) (b : BitVec 64) : BitVec 64×BitVec 64:=
  wordAddCarryHOL (scalarThirdHigh a b).1 (Mul64.parts (a 3) b).1 0#64
def scalarFourth (a : Input.RlpWrite.U256Value.Words) (b : BitVec 64) : BitVec 64×BitVec 64:=
  wordAddCarryHOL ((scalarThirdHigh a b).2+(scalarThird a b).2) (Mul64.parts (a 3) b).2 0#64

def scalarValue (a : Input.RlpWrite.U256Value.Words) (b : BitVec 64) : ValueHOL 64:=
  .rStruct [.val (.word (Mul64.parts (a 0) b).1),.val (.word (scalarFirst a b).1),
    .val (.word (scalarSecond a b).1),.val (.word (scalarThird a b).1),
    .val (.word (scalarFourth a b).1),.val (.word (scalarFourth a b).2),.val (.word 0#64),.val (.word 0#64)]

private theorem carry_right_zero (a : BitVec 64) : wordAddCarryHOL a 0#64 0#64=(a,0#64) := by
  have inside:=a.isLt
  simp [wordAddCarryHOL] <;> omega

private theorem carry_left_zero (a : BitVec 64) : wordAddCarryHOL 0#64 a 0#64=(a,0#64) := by
  have inside:=a.isLt
  simp [wordAddCarryHOL] <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
/-- Actual straight-line accumulation after the sixteen original products,
specialized to the scalar right operand used by Taylor. -/
theorem scalar_tail (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (a : Input.RlpWrite.U256Value.Words) (b : BitVec 64)
    (p00 : source.locals.lookup (ofString "p00")=some (Mul64.value (a 0) b))
    (p01 : source.locals.lookup (ofString "p01")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]))
    (p02 : source.locals.lookup (ofString "p02")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]))
    (p03 : source.locals.lookup (ofString "p03")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]))
    (p10 : source.locals.lookup (ofString "p10")=some (Mul64.value (a 1) b))
    (p11 : source.locals.lookup (ofString "p11")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]))
    (p12 : source.locals.lookup (ofString "p12")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]))
    (p13 : source.locals.lookup (ofString "p13")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]))
    (p20 : source.locals.lookup (ofString "p20")=some (Mul64.value (a 2) b))
    (p21 : source.locals.lookup (ofString "p21")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]))
    (p22 : source.locals.lookup (ofString "p22")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]))
    (p23 : source.locals.lookup (ofString "p23")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]))
    (p30 : source.locals.lookup (ofString "p30")=some (Mul64.value (a 3) b))
    (p31 : source.locals.lookup (ofString "p31")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]))
    (p32 : source.locals.lookup (ofString "p32")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]))
    (p33 : source.locals.lookup (ofString "p33")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]))
    : Input.PureStraight.Returns source afterProducts (scalarValue a b) := by
  classical
  simp only [afterProducts,dropProductCalls,fullBody,ArithmeticEffects.Kind.body,ArithmeticEffects.Kind.signature,
    ArithmeticEffects.Kind.original,Guest.guestFn_u256_mul_full,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  have p00Read : source.locals.lookup (MlString.implode [112#8,48#8,48#8])=some (Mul64.value (a 0) b):=p00
  have p01Read : source.locals.lookup (MlString.implode [112#8,48#8,49#8])=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=p01
  have p02Read : source.locals.lookup (MlString.implode [112#8,48#8,50#8])=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=p02
  have p03Read : source.locals.lookup (MlString.implode [112#8,48#8,51#8])=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=p03
  have p10Read : source.locals.lookup (MlString.implode [112#8,49#8,48#8])=some (Mul64.value (a 1) b):=p10
  have p11Read : source.locals.lookup (MlString.implode [112#8,49#8,49#8])=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=p11
  have p12Read : source.locals.lookup (MlString.implode [112#8,49#8,50#8])=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=p12
  have p13Read : source.locals.lookup (MlString.implode [112#8,49#8,51#8])=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=p13
  have p20Read : source.locals.lookup (MlString.implode [112#8,50#8,48#8])=some (Mul64.value (a 2) b):=p20
  have p21Read : source.locals.lookup (MlString.implode [112#8,50#8,49#8])=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=p21
  have p22Read : source.locals.lookup (MlString.implode [112#8,50#8,50#8])=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=p22
  have p23Read : source.locals.lookup (MlString.implode [112#8,50#8,51#8])=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=p23
  have p30Read : source.locals.lookup (MlString.implode [112#8,51#8,48#8])=some (Mul64.value (a 3) b):=p30
  have p31Read : source.locals.lookup (MlString.implode [112#8,51#8,49#8])=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=p31
  have p32Read : source.locals.lookup (MlString.implode [112#8,51#8,50#8])=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=p32
  have p33Read : source.locals.lookup (MlString.implode [112#8,51#8,51#8])=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=p33
  refine Input.PureStraight.declares (.rStruct [.val (.word 0#64),.val (.word 0#64)]) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read] <;> rfl
  generalize eq1 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word 0#64),.val (.word 0#64)]) source=s1
  have lookup1 (key : MlS) : s1.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word 0#64),.val (.word 0#64)]) else source.locals.lookup key):=by
    rw [←eq1]
    rfl
  refine Input.PureStraight.declares (.val (.word 0#64)) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read] <;> rfl
  generalize eq2 : setVarHOLFinite (ofString "acc") (.val (.word 0#64)) s1=s2
  have lookup2 (key : MlS) : s2.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word 0#64)) else s1.locals.lookup key):=by
    rw [←eq2]
    rfl
  refine Input.PureStraight.declares (.val (.word 0#64)) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read] <;> rfl
  generalize eq3 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s2=s3
  have lookup3 (key : MlS) : s3.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s2.locals.lookup key):=by
    rw [←eq3]
    rfl
  refine Input.PureStraight.declares (.val (.word ((Mul64.parts (a 0) b).1))) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read] <;> rfl
  generalize eq4 : setVarHOLFinite (ofString "r0") (.val (.word ((Mul64.parts (a 0) b).1))) s3=s4
  have lookup4 (key : MlS) : s4.locals.lookup key=
      (if ofString "r0"==key then some (.val (.word ((Mul64.parts (a 0) b).1))) else s3.locals.lookup key):=by
    rw [←eq4]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word ((Mul64.parts (a 0) b).2))) s4) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read] <;> rfl
  generalize eq5 : setVarHOLFinite (ofString "acc") (.val (.word ((Mul64.parts (a 0) b).2))) s4=s5
  have lookup5 (key : MlS) : s5.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word ((Mul64.parts (a 0) b).2))) else s4.locals.lookup key):=by
    rw [←eq5]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word ((Mul64.parts (a 0) b).2)),.val (.word 0#64)]) s5) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read] <;> rfl
  generalize eq6 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word ((Mul64.parts (a 0) b).2)),.val (.word 0#64)]) s5=s6
  have lookup6 (key : MlS) : s6.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word ((Mul64.parts (a 0) b).2)),.val (.word 0#64)]) else s5.locals.lookup key):=by
    rw [←eq6]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word ((Mul64.parts (a 0) b).2))) s6) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read] <;> rfl
  generalize eq7 : setVarHOLFinite (ofString "acc") (.val (.word ((Mul64.parts (a 0) b).2))) s6=s7
  have lookup7 (key : MlS) : s7.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word ((Mul64.parts (a 0) b).2))) else s6.locals.lookup key):=by
    rw [←eq7]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s7) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read] <;> rfl
  generalize eq8 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s7=s8
  have lookup8 (key : MlS) : s8.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s7.locals.lookup key):=by
    rw [←eq8]
    rfl
  let c1:=wordAddCarryHOL ((Mul64.parts (a 0) b).2) ((Mul64.parts (a 1) b).1) 0#64
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c1.1),.val (.word c1.2)]) s8) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1] <;> rfl
  generalize eq9 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c1.1),.val (.word c1.2)]) s8=s9
  have lookup9 (key : MlS) : s9.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c1.1),.val (.word c1.2)]) else s8.locals.lookup key):=by
    rw [←eq9]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c1.1)) s9) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1] <;> rfl
  generalize eq10 : setVarHOLFinite (ofString "acc") (.val (.word c1.1)) s9=s10
  have lookup10 (key : MlS) : s10.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c1.1)) else s9.locals.lookup key):=by
    rw [←eq10]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word c1.2)) s10) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1] <;> rfl
  generalize eq11 : setVarHOLFinite (ofString "hi") (.val (.word c1.2)) s10=s11
  have lookup11 (key : MlS) : s11.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word c1.2)) else s10.locals.lookup key):=by
    rw [←eq11]
    rfl
  refine Input.PureStraight.declares (.val (.word c1.1)) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1] <;> rfl
  generalize eq12 : setVarHOLFinite (ofString "r1") (.val (.word c1.1)) s11=s12
  have lookup12 (key : MlS) : s12.locals.lookup key=
      (if ofString "r1"==key then some (.val (.word c1.1)) else s11.locals.lookup key):=by
    rw [←eq12]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c1.2)) s12) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1] <;> rfl
  generalize eq13 : setVarHOLFinite (ofString "acc") (.val (.word c1.2)) s12=s13
  have lookup13 (key : MlS) : s13.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c1.2)) else s12.locals.lookup key):=by
    rw [←eq13]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s13) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1] <;> rfl
  generalize eq14 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s13=s14
  have lookup14 (key : MlS) : s14.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s13.locals.lookup key):=by
    rw [←eq14]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c1.2),.val (.word 0#64)]) s14) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1] <;> rfl
  generalize eq15 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c1.2),.val (.word 0#64)]) s14=s15
  have lookup15 (key : MlS) : s15.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c1.2),.val (.word 0#64)]) else s14.locals.lookup key):=by
    rw [←eq15]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c1.2)) s15) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1] <;> rfl
  generalize eq16 : setVarHOLFinite (ofString "acc") (.val (.word c1.2)) s15=s16
  have lookup16 (key : MlS) : s16.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c1.2)) else s15.locals.lookup key):=by
    rw [←eq16]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s16) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1] <;> rfl
  generalize eq17 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s16=s17
  have lookup17 (key : MlS) : s17.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s16.locals.lookup key):=by
    rw [←eq17]
    rfl
  let c2:=wordAddCarryHOL c1.2 ((Mul64.parts (a 1) b).2) 0#64
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c2.1),.val (.word c2.2)]) s17) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2] <;> rfl
  generalize eq18 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c2.1),.val (.word c2.2)]) s17=s18
  have lookup18 (key : MlS) : s18.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c2.1),.val (.word c2.2)]) else s17.locals.lookup key):=by
    rw [←eq18]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c2.1)) s18) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2] <;> rfl
  generalize eq19 : setVarHOLFinite (ofString "acc") (.val (.word c2.1)) s18=s19
  have lookup19 (key : MlS) : s19.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c2.1)) else s18.locals.lookup key):=by
    rw [←eq19]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word c2.2)) s19) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2] <;> rfl
  generalize eq20 : setVarHOLFinite (ofString "hi") (.val (.word c2.2)) s19=s20
  have lookup20 (key : MlS) : s20.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word c2.2)) else s19.locals.lookup key):=by
    rw [←eq20]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c2.1),.val (.word 0#64)]) s20) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2] <;> rfl
  generalize eq21 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c2.1),.val (.word 0#64)]) s20=s21
  have lookup21 (key : MlS) : s21.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c2.1),.val (.word 0#64)]) else s20.locals.lookup key):=by
    rw [←eq21]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c2.1)) s21) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2] <;> rfl
  generalize eq22 : setVarHOLFinite (ofString "acc") (.val (.word c2.1)) s21=s22
  have lookup22 (key : MlS) : s22.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c2.1)) else s21.locals.lookup key):=by
    rw [←eq22]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word c2.2)) s22) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2] <;> rfl
  generalize eq23 : setVarHOLFinite (ofString "hi") (.val (.word c2.2)) s22=s23
  have lookup23 (key : MlS) : s23.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word c2.2)) else s22.locals.lookup key):=by
    rw [←eq23]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c2.1),.val (.word 0#64)]) s23) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2] <;> rfl
  generalize eq24 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c2.1),.val (.word 0#64)]) s23=s24
  have lookup24 (key : MlS) : s24.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c2.1),.val (.word 0#64)]) else s23.locals.lookup key):=by
    rw [←eq24]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c2.1)) s24) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2] <;> rfl
  generalize eq25 : setVarHOLFinite (ofString "acc") (.val (.word c2.1)) s24=s25
  have lookup25 (key : MlS) : s25.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c2.1)) else s24.locals.lookup key):=by
    rw [←eq25]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word c2.2)) s25) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2] <;> rfl
  generalize eq26 : setVarHOLFinite (ofString "hi") (.val (.word c2.2)) s25=s26
  have lookup26 (key : MlS) : s26.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word c2.2)) else s25.locals.lookup key):=by
    rw [←eq26]
    rfl
  let c3:=wordAddCarryHOL c2.1 ((Mul64.parts (a 2) b).1) 0#64
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c3.1),.val (.word c3.2)]) s26) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3] <;> rfl
  generalize eq27 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c3.1),.val (.word c3.2)]) s26=s27
  have lookup27 (key : MlS) : s27.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c3.1),.val (.word c3.2)]) else s26.locals.lookup key):=by
    rw [←eq27]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c3.1)) s27) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3] <;> rfl
  generalize eq28 : setVarHOLFinite (ofString "acc") (.val (.word c3.1)) s27=s28
  have lookup28 (key : MlS) : s28.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c3.1)) else s27.locals.lookup key):=by
    rw [←eq28]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word (c2.2+c3.2))) s28) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3] <;> rfl
  generalize eq29 : setVarHOLFinite (ofString "hi") (.val (.word (c2.2+c3.2))) s28=s29
  have lookup29 (key : MlS) : s29.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word (c2.2+c3.2))) else s28.locals.lookup key):=by
    rw [←eq29]
    rfl
  refine Input.PureStraight.declares (.val (.word c3.1)) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3] <;> rfl
  generalize eq30 : setVarHOLFinite (ofString "r2") (.val (.word c3.1)) s29=s30
  have lookup30 (key : MlS) : s30.locals.lookup key=
      (if ofString "r2"==key then some (.val (.word c3.1)) else s29.locals.lookup key):=by
    rw [←eq30]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word (c2.2+c3.2))) s30) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3] <;> rfl
  generalize eq31 : setVarHOLFinite (ofString "acc") (.val (.word (c2.2+c3.2))) s30=s31
  have lookup31 (key : MlS) : s31.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word (c2.2+c3.2))) else s30.locals.lookup key):=by
    rw [←eq31]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s31) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3] <;> rfl
  generalize eq32 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s31=s32
  have lookup32 (key : MlS) : s32.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s31.locals.lookup key):=by
    rw [←eq32]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word (c2.2+c3.2)),.val (.word 0#64)]) s32) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3] <;> rfl
  generalize eq33 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word (c2.2+c3.2)),.val (.word 0#64)]) s32=s33
  have lookup33 (key : MlS) : s33.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word (c2.2+c3.2)),.val (.word 0#64)]) else s32.locals.lookup key):=by
    rw [←eq33]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word (c2.2+c3.2))) s33) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3] <;> rfl
  generalize eq34 : setVarHOLFinite (ofString "acc") (.val (.word (c2.2+c3.2))) s33=s34
  have lookup34 (key : MlS) : s34.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word (c2.2+c3.2))) else s33.locals.lookup key):=by
    rw [←eq34]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s34) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3] <;> rfl
  generalize eq35 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s34=s35
  have lookup35 (key : MlS) : s35.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s34.locals.lookup key):=by
    rw [←eq35]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word (c2.2+c3.2)),.val (.word 0#64)]) s35) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3] <;> rfl
  generalize eq36 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word (c2.2+c3.2)),.val (.word 0#64)]) s35=s36
  have lookup36 (key : MlS) : s36.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word (c2.2+c3.2)),.val (.word 0#64)]) else s35.locals.lookup key):=by
    rw [←eq36]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word (c2.2+c3.2))) s36) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3] <;> rfl
  generalize eq37 : setVarHOLFinite (ofString "acc") (.val (.word (c2.2+c3.2))) s36=s37
  have lookup37 (key : MlS) : s37.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word (c2.2+c3.2))) else s36.locals.lookup key):=by
    rw [←eq37]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s37) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3] <;> rfl
  generalize eq38 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s37=s38
  have lookup38 (key : MlS) : s38.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s37.locals.lookup key):=by
    rw [←eq38]
    rfl
  let c4:=wordAddCarryHOL (c2.2+c3.2) ((Mul64.parts (a 2) b).2) 0#64
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c4.1),.val (.word c4.2)]) s38) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4] <;> rfl
  generalize eq39 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c4.1),.val (.word c4.2)]) s38=s39
  have lookup39 (key : MlS) : s39.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c4.1),.val (.word c4.2)]) else s38.locals.lookup key):=by
    rw [←eq39]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c4.1)) s39) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4] <;> rfl
  generalize eq40 : setVarHOLFinite (ofString "acc") (.val (.word c4.1)) s39=s40
  have lookup40 (key : MlS) : s40.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c4.1)) else s39.locals.lookup key):=by
    rw [←eq40]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word c4.2)) s40) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4] <;> rfl
  generalize eq41 : setVarHOLFinite (ofString "hi") (.val (.word c4.2)) s40=s41
  have lookup41 (key : MlS) : s41.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word c4.2)) else s40.locals.lookup key):=by
    rw [←eq41]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c4.1),.val (.word 0#64)]) s41) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4] <;> rfl
  generalize eq42 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c4.1),.val (.word 0#64)]) s41=s42
  have lookup42 (key : MlS) : s42.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c4.1),.val (.word 0#64)]) else s41.locals.lookup key):=by
    rw [←eq42]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c4.1)) s42) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4] <;> rfl
  generalize eq43 : setVarHOLFinite (ofString "acc") (.val (.word c4.1)) s42=s43
  have lookup43 (key : MlS) : s43.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c4.1)) else s42.locals.lookup key):=by
    rw [←eq43]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word c4.2)) s43) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4] <;> rfl
  generalize eq44 : setVarHOLFinite (ofString "hi") (.val (.word c4.2)) s43=s44
  have lookup44 (key : MlS) : s44.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word c4.2)) else s43.locals.lookup key):=by
    rw [←eq44]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c4.1),.val (.word 0#64)]) s44) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4] <;> rfl
  generalize eq45 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c4.1),.val (.word 0#64)]) s44=s45
  have lookup45 (key : MlS) : s45.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c4.1),.val (.word 0#64)]) else s44.locals.lookup key):=by
    rw [←eq45]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c4.1)) s45) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4] <;> rfl
  generalize eq46 : setVarHOLFinite (ofString "acc") (.val (.word c4.1)) s45=s46
  have lookup46 (key : MlS) : s46.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c4.1)) else s45.locals.lookup key):=by
    rw [←eq46]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word c4.2)) s46) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4] <;> rfl
  generalize eq47 : setVarHOLFinite (ofString "hi") (.val (.word c4.2)) s46=s47
  have lookup47 (key : MlS) : s47.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word c4.2)) else s46.locals.lookup key):=by
    rw [←eq47]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c4.1),.val (.word 0#64)]) s47) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4] <;> rfl
  generalize eq48 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c4.1),.val (.word 0#64)]) s47=s48
  have lookup48 (key : MlS) : s48.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c4.1),.val (.word 0#64)]) else s47.locals.lookup key):=by
    rw [←eq48]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c4.1)) s48) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4] <;> rfl
  generalize eq49 : setVarHOLFinite (ofString "acc") (.val (.word c4.1)) s48=s49
  have lookup49 (key : MlS) : s49.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c4.1)) else s48.locals.lookup key):=by
    rw [←eq49]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word c4.2)) s49) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4] <;> rfl
  generalize eq50 : setVarHOLFinite (ofString "hi") (.val (.word c4.2)) s49=s50
  have lookup50 (key : MlS) : s50.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word c4.2)) else s49.locals.lookup key):=by
    rw [←eq50]
    rfl
  let c5:=wordAddCarryHOL c4.1 ((Mul64.parts (a 3) b).1) 0#64
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c5.1),.val (.word c5.2)]) s50) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5] <;> rfl
  generalize eq51 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c5.1),.val (.word c5.2)]) s50=s51
  have lookup51 (key : MlS) : s51.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c5.1),.val (.word c5.2)]) else s50.locals.lookup key):=by
    rw [←eq51]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c5.1)) s51) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5] <;> rfl
  generalize eq52 : setVarHOLFinite (ofString "acc") (.val (.word c5.1)) s51=s52
  have lookup52 (key : MlS) : s52.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c5.1)) else s51.locals.lookup key):=by
    rw [←eq52]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word (c4.2+c5.2))) s52) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5] <;> rfl
  generalize eq53 : setVarHOLFinite (ofString "hi") (.val (.word (c4.2+c5.2))) s52=s53
  have lookup53 (key : MlS) : s53.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word (c4.2+c5.2))) else s52.locals.lookup key):=by
    rw [←eq53]
    rfl
  refine Input.PureStraight.declares (.val (.word c5.1)) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5] <;> rfl
  generalize eq54 : setVarHOLFinite (ofString "r3") (.val (.word c5.1)) s53=s54
  have lookup54 (key : MlS) : s54.locals.lookup key=
      (if ofString "r3"==key then some (.val (.word c5.1)) else s53.locals.lookup key):=by
    rw [←eq54]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word (c4.2+c5.2))) s54) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5] <;> rfl
  generalize eq55 : setVarHOLFinite (ofString "acc") (.val (.word (c4.2+c5.2))) s54=s55
  have lookup55 (key : MlS) : s55.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word (c4.2+c5.2))) else s54.locals.lookup key):=by
    rw [←eq55]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s55) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5] <;> rfl
  generalize eq56 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s55=s56
  have lookup56 (key : MlS) : s56.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s55.locals.lookup key):=by
    rw [←eq56]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word (c4.2+c5.2)),.val (.word 0#64)]) s56) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5] <;> rfl
  generalize eq57 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word (c4.2+c5.2)),.val (.word 0#64)]) s56=s57
  have lookup57 (key : MlS) : s57.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word (c4.2+c5.2)),.val (.word 0#64)]) else s56.locals.lookup key):=by
    rw [←eq57]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word (c4.2+c5.2))) s57) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5] <;> rfl
  generalize eq58 : setVarHOLFinite (ofString "acc") (.val (.word (c4.2+c5.2))) s57=s58
  have lookup58 (key : MlS) : s58.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word (c4.2+c5.2))) else s57.locals.lookup key):=by
    rw [←eq58]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s58) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5] <;> rfl
  generalize eq59 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s58=s59
  have lookup59 (key : MlS) : s59.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s58.locals.lookup key):=by
    rw [←eq59]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word (c4.2+c5.2)),.val (.word 0#64)]) s59) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5] <;> rfl
  generalize eq60 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word (c4.2+c5.2)),.val (.word 0#64)]) s59=s60
  have lookup60 (key : MlS) : s60.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word (c4.2+c5.2)),.val (.word 0#64)]) else s59.locals.lookup key):=by
    rw [←eq60]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word (c4.2+c5.2))) s60) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5] <;> rfl
  generalize eq61 : setVarHOLFinite (ofString "acc") (.val (.word (c4.2+c5.2))) s60=s61
  have lookup61 (key : MlS) : s61.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word (c4.2+c5.2))) else s60.locals.lookup key):=by
    rw [←eq61]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s61) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5] <;> rfl
  generalize eq62 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s61=s62
  have lookup62 (key : MlS) : s62.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s61.locals.lookup key):=by
    rw [←eq62]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word (c4.2+c5.2)),.val (.word 0#64)]) s62) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5] <;> rfl
  generalize eq63 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word (c4.2+c5.2)),.val (.word 0#64)]) s62=s63
  have lookup63 (key : MlS) : s63.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word (c4.2+c5.2)),.val (.word 0#64)]) else s62.locals.lookup key):=by
    rw [←eq63]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word (c4.2+c5.2))) s63) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5] <;> rfl
  generalize eq64 : setVarHOLFinite (ofString "acc") (.val (.word (c4.2+c5.2))) s63=s64
  have lookup64 (key : MlS) : s64.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word (c4.2+c5.2))) else s63.locals.lookup key):=by
    rw [←eq64]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s64) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5] <;> rfl
  generalize eq65 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s64=s65
  have lookup65 (key : MlS) : s65.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s64.locals.lookup key):=by
    rw [←eq65]
    rfl
  let c6:=wordAddCarryHOL (c4.2+c5.2) ((Mul64.parts (a 3) b).2) 0#64
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.1),.val (.word c6.2)]) s65) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq66 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.1),.val (.word c6.2)]) s65=s66
  have lookup66 (key : MlS) : s66.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c6.1),.val (.word c6.2)]) else s65.locals.lookup key):=by
    rw [←eq66]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c6.1)) s66) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq67 : setVarHOLFinite (ofString "acc") (.val (.word c6.1)) s66=s67
  have lookup67 (key : MlS) : s67.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c6.1)) else s66.locals.lookup key):=by
    rw [←eq67]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word c6.2)) s67) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq68 : setVarHOLFinite (ofString "hi") (.val (.word c6.2)) s67=s68
  have lookup68 (key : MlS) : s68.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word c6.2)) else s67.locals.lookup key):=by
    rw [←eq68]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.1),.val (.word 0#64)]) s68) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq69 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.1),.val (.word 0#64)]) s68=s69
  have lookup69 (key : MlS) : s69.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c6.1),.val (.word 0#64)]) else s68.locals.lookup key):=by
    rw [←eq69]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c6.1)) s69) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq70 : setVarHOLFinite (ofString "acc") (.val (.word c6.1)) s69=s70
  have lookup70 (key : MlS) : s70.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c6.1)) else s69.locals.lookup key):=by
    rw [←eq70]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word c6.2)) s70) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq71 : setVarHOLFinite (ofString "hi") (.val (.word c6.2)) s70=s71
  have lookup71 (key : MlS) : s71.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word c6.2)) else s70.locals.lookup key):=by
    rw [←eq71]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.1),.val (.word 0#64)]) s71) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq72 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.1),.val (.word 0#64)]) s71=s72
  have lookup72 (key : MlS) : s72.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c6.1),.val (.word 0#64)]) else s71.locals.lookup key):=by
    rw [←eq72]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c6.1)) s72) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq73 : setVarHOLFinite (ofString "acc") (.val (.word c6.1)) s72=s73
  have lookup73 (key : MlS) : s73.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c6.1)) else s72.locals.lookup key):=by
    rw [←eq73]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word c6.2)) s73) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq74 : setVarHOLFinite (ofString "hi") (.val (.word c6.2)) s73=s74
  have lookup74 (key : MlS) : s74.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word c6.2)) else s73.locals.lookup key):=by
    rw [←eq74]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.1),.val (.word 0#64)]) s74) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq75 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.1),.val (.word 0#64)]) s74=s75
  have lookup75 (key : MlS) : s75.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c6.1),.val (.word 0#64)]) else s74.locals.lookup key):=by
    rw [←eq75]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c6.1)) s75) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq76 : setVarHOLFinite (ofString "acc") (.val (.word c6.1)) s75=s76
  have lookup76 (key : MlS) : s76.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c6.1)) else s75.locals.lookup key):=by
    rw [←eq76]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word c6.2)) s76) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq77 : setVarHOLFinite (ofString "hi") (.val (.word c6.2)) s76=s77
  have lookup77 (key : MlS) : s77.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word c6.2)) else s76.locals.lookup key):=by
    rw [←eq77]
    rfl
  refine Input.PureStraight.declares (.val (.word c6.1)) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq78 : setVarHOLFinite (ofString "r4") (.val (.word c6.1)) s77=s78
  have lookup78 (key : MlS) : s78.locals.lookup key=
      (if ofString "r4"==key then some (.val (.word c6.1)) else s77.locals.lookup key):=by
    rw [←eq78]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c6.2)) s78) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq79 : setVarHOLFinite (ofString "acc") (.val (.word c6.2)) s78=s79
  have lookup79 (key : MlS) : s79.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c6.2)) else s78.locals.lookup key):=by
    rw [←eq79]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s79) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq80 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s79=s80
  have lookup80 (key : MlS) : s80.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s79.locals.lookup key):=by
    rw [←eq80]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.2),.val (.word 0#64)]) s80) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq81 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.2),.val (.word 0#64)]) s80=s81
  have lookup81 (key : MlS) : s81.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c6.2),.val (.word 0#64)]) else s80.locals.lookup key):=by
    rw [←eq81]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c6.2)) s81) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq82 : setVarHOLFinite (ofString "acc") (.val (.word c6.2)) s81=s82
  have lookup82 (key : MlS) : s82.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c6.2)) else s81.locals.lookup key):=by
    rw [←eq82]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s82) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq83 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s82=s83
  have lookup83 (key : MlS) : s83.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s82.locals.lookup key):=by
    rw [←eq83]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.2),.val (.word 0#64)]) s83) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq84 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.2),.val (.word 0#64)]) s83=s84
  have lookup84 (key : MlS) : s84.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c6.2),.val (.word 0#64)]) else s83.locals.lookup key):=by
    rw [←eq84]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c6.2)) s84) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq85 : setVarHOLFinite (ofString "acc") (.val (.word c6.2)) s84=s85
  have lookup85 (key : MlS) : s85.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c6.2)) else s84.locals.lookup key):=by
    rw [←eq85]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s85) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq86 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s85=s86
  have lookup86 (key : MlS) : s86.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s85.locals.lookup key):=by
    rw [←eq86]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.2),.val (.word 0#64)]) s86) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq87 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.2),.val (.word 0#64)]) s86=s87
  have lookup87 (key : MlS) : s87.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c6.2),.val (.word 0#64)]) else s86.locals.lookup key):=by
    rw [←eq87]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c6.2)) s87) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq88 : setVarHOLFinite (ofString "acc") (.val (.word c6.2)) s87=s88
  have lookup88 (key : MlS) : s88.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c6.2)) else s87.locals.lookup key):=by
    rw [←eq88]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s88) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq89 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s88=s89
  have lookup89 (key : MlS) : s89.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s88.locals.lookup key):=by
    rw [←eq89]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.2),.val (.word 0#64)]) s89) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq90 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.2),.val (.word 0#64)]) s89=s90
  have lookup90 (key : MlS) : s90.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c6.2),.val (.word 0#64)]) else s89.locals.lookup key):=by
    rw [←eq90]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c6.2)) s90) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq91 : setVarHOLFinite (ofString "acc") (.val (.word c6.2)) s90=s91
  have lookup91 (key : MlS) : s91.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c6.2)) else s90.locals.lookup key):=by
    rw [←eq91]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s91) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq92 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s91=s92
  have lookup92 (key : MlS) : s92.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s91.locals.lookup key):=by
    rw [←eq92]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.2),.val (.word 0#64)]) s92) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq93 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word c6.2),.val (.word 0#64)]) s92=s93
  have lookup93 (key : MlS) : s93.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word c6.2),.val (.word 0#64)]) else s92.locals.lookup key):=by
    rw [←eq93]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word c6.2)) s93) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq94 : setVarHOLFinite (ofString "acc") (.val (.word c6.2)) s93=s94
  have lookup94 (key : MlS) : s94.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word c6.2)) else s93.locals.lookup key):=by
    rw [←eq94]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s94) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq95 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s94=s95
  have lookup95 (key : MlS) : s95.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s94.locals.lookup key):=by
    rw [←eq95]
    rfl
  refine Input.PureStraight.declares (.val (.word c6.2)) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup95,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq96 : setVarHOLFinite (ofString "r5") (.val (.word c6.2)) s95=s96
  have lookup96 (key : MlS) : s96.locals.lookup key=
      (if ofString "r5"==key then some (.val (.word c6.2)) else s95.locals.lookup key):=by
    rw [←eq96]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word 0#64)) s96) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup96,lookup95,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq97 : setVarHOLFinite (ofString "acc") (.val (.word 0#64)) s96=s97
  have lookup97 (key : MlS) : s97.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word 0#64)) else s96.locals.lookup key):=by
    rw [←eq97]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s97) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup97,lookup96,lookup95,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq98 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s97=s98
  have lookup98 (key : MlS) : s98.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s97.locals.lookup key):=by
    rw [←eq98]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word 0#64),.val (.word 0#64)]) s98) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup98,lookup97,lookup96,lookup95,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq99 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word 0#64),.val (.word 0#64)]) s98=s99
  have lookup99 (key : MlS) : s99.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word 0#64),.val (.word 0#64)]) else s98.locals.lookup key):=by
    rw [←eq99]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word 0#64)) s99) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup99,lookup98,lookup97,lookup96,lookup95,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq100 : setVarHOLFinite (ofString "acc") (.val (.word 0#64)) s99=s100
  have lookup100 (key : MlS) : s100.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word 0#64)) else s99.locals.lookup key):=by
    rw [←eq100]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s100) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup100,lookup99,lookup98,lookup97,lookup96,lookup95,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq101 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s100=s101
  have lookup101 (key : MlS) : s101.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s100.locals.lookup key):=by
    rw [←eq101]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word 0#64),.val (.word 0#64)]) s101) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup101,lookup100,lookup99,lookup98,lookup97,lookup96,lookup95,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq102 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word 0#64),.val (.word 0#64)]) s101=s102
  have lookup102 (key : MlS) : s102.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word 0#64),.val (.word 0#64)]) else s101.locals.lookup key):=by
    rw [←eq102]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word 0#64)) s102) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup102,lookup101,lookup100,lookup99,lookup98,lookup97,lookup96,lookup95,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq103 : setVarHOLFinite (ofString "acc") (.val (.word 0#64)) s102=s103
  have lookup103 (key : MlS) : s103.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word 0#64)) else s102.locals.lookup key):=by
    rw [←eq103]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s103) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup103,lookup102,lookup101,lookup100,lookup99,lookup98,lookup97,lookup96,lookup95,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq104 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s103=s104
  have lookup104 (key : MlS) : s104.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s103.locals.lookup key):=by
    rw [←eq104]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "t") (.rStruct [.val (.word 0#64),.val (.word 0#64)]) s104) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_primitive,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup104,lookup103,lookup102,lookup101,lookup100,lookup99,lookup98,lookup97,lookup96,lookup95,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq105 : setVarHOLFinite (ofString "t") (.rStruct [.val (.word 0#64),.val (.word 0#64)]) s104=s105
  have lookup105 (key : MlS) : s105.locals.lookup key=
      (if ofString "t"==key then some (.rStruct [.val (.word 0#64),.val (.word 0#64)]) else s104.locals.lookup key):=by
    rw [←eq105]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word 0#64)) s105) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup105,lookup104,lookup103,lookup102,lookup101,lookup100,lookup99,lookup98,lookup97,lookup96,lookup95,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq106 : setVarHOLFinite (ofString "acc") (.val (.word 0#64)) s105=s106
  have lookup106 (key : MlS) : s106.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word 0#64)) else s105.locals.lookup key):=by
    rw [←eq106]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s106) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup106,lookup105,lookup104,lookup103,lookup102,lookup101,lookup100,lookup99,lookup98,lookup97,lookup96,lookup95,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq107 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s106=s107
  have lookup107 (key : MlS) : s107.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s106.locals.lookup key):=by
    rw [←eq107]
    rfl
  refine Input.PureStraight.declares (.val (.word 0#64)) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup107,lookup106,lookup105,lookup104,lookup103,lookup102,lookup101,lookup100,lookup99,lookup98,lookup97,lookup96,lookup95,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq108 : setVarHOLFinite (ofString "r6") (.val (.word 0#64)) s107=s108
  have lookup108 (key : MlS) : s108.locals.lookup key=
      (if ofString "r6"==key then some (.val (.word 0#64)) else s107.locals.lookup key):=by
    rw [←eq108]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "acc") (.val (.word 0#64)) s108) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup108,lookup107,lookup106,lookup105,lookup104,lookup103,lookup102,lookup101,lookup100,lookup99,lookup98,lookup97,lookup96,lookup95,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq109 : setVarHOLFinite (ofString "acc") (.val (.word 0#64)) s108=s109
  have lookup109 (key : MlS) : s109.locals.lookup key=
      (if ofString "acc"==key then some (.val (.word 0#64)) else s108.locals.lookup key):=by
    rw [←eq109]
    rfl
  refine Input.PureStraight.command (middle:=setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s109) ?_ rfl ?_
  · simp [evaluateHOLFiniteState_assign,panPrimopHOLExact,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup109,lookup108,lookup107,lookup106,lookup105,lookup104,lookup103,lookup102,lookup101,lookup100,lookup99,lookup98,lookup97,lookup96,lookup95,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq110 : setVarHOLFinite (ofString "hi") (.val (.word 0#64)) s109=s110
  have lookup110 (key : MlS) : s110.locals.lookup key=
      (if ofString "hi"==key then some (.val (.word 0#64)) else s109.locals.lookup key):=by
    rw [←eq110]
    rfl
  refine Input.PureStraight.declares (.val (.word 0#64)) ?_ (by simp [shapeOfHOLExact,shapeEqHOL_eq_true]) ?_
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup110,lookup109,lookup108,lookup107,lookup106,lookup105,lookup104,lookup103,lookup102,lookup101,lookup100,lookup99,lookup98,lookup97,lookup96,lookup95,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6] <;> rfl
  generalize eq111 : setVarHOLFinite (ofString "r7") (.val (.word 0#64)) s110=s111
  have lookup111 (key : MlS) : s111.locals.lookup key=
      (if ofString "r7"==key then some (.val (.word 0#64)) else s110.locals.lookup key):=by
    rw [←eq111]
    rfl
  refine ⟨emptyLocalsHOLFinite _,?_,rfl⟩
  simp [evaluateHOLFiniteState_return,scalarValue,scalarFirst,scalarSecondHigh,scalarSecond,scalarThirdHigh,scalarThird,scalarFourth,sizeOfShapeWithContextHOL,evalHOLExact,evalListHOLExact,evalListHOLFinite,toExact,ofString,localVar,setVarHOLFinite,setKvarHOLFinite,HolFiniteMapExact.update,FUPDATE,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL_eq_true,valueWord,valueIsWord,wordOpHOL,wordOp,carry_right_zero,carry_left_zero,Mul64.value,lookup111,lookup110,lookup109,lookup108,lookup107,lookup106,lookup105,lookup104,lookup103,lookup102,lookup101,lookup100,lookup99,lookup98,lookup97,lookup96,lookup95,lookup94,lookup93,lookup92,lookup91,lookup90,lookup89,lookup88,lookup87,lookup86,lookup85,lookup84,lookup83,lookup82,lookup81,lookup80,lookup79,lookup78,lookup77,lookup76,lookup75,lookup74,lookup73,lookup72,lookup71,lookup70,lookup69,lookup68,lookup67,lookup66,lookup65,lookup64,lookup63,lookup62,lookup61,lookup60,lookup59,lookup58,lookup57,lookup56,lookup55,lookup54,lookup53,lookup52,lookup51,lookup50,lookup49,lookup48,lookup47,lookup46,lookup45,lookup44,lookup43,lookup42,lookup41,lookup40,lookup39,lookup38,lookup37,lookup36,lookup35,lookup34,lookup33,lookup32,lookup31,lookup30,lookup29,lookup28,lookup27,lookup26,lookup25,lookup24,lookup23,lookup22,lookup21,lookup20,lookup19,lookup18,lookup17,lookup16,lookup15,lookup14,lookup13,lookup12,lookup11,lookup10,lookup9,lookup8,lookup7,lookup6,lookup5,lookup4,lookup3,lookup2,lookup1,p00Read,p01Read,p02Read,p03Read,p10Read,p11Read,p12Read,p13Read,p20Read,p21Read,p22Read,p23Read,p30Read,p31Read,p32Read,p33Read,c1,c2,c3,c4,c5,c6]

end InitECandidate.Solver.GasBudget.U256Multiply

#print axioms InitECandidate.Solver.GasBudget.U256Multiply.scalar_tail

namespace InitECandidate.Solver.GasBudget.U256Multiply
open Flapjack

private theorem carry_flag_bound (left right : BitVec 64) :
    (wordAddCarryHOL left right 0#64).2.toNat≤1 := by
  have represented:=Mul64.carry_number left right
  have leftBound:=left.isLt
  have rightBound:=right.isLt
  omega

private theorem carry_flags_number (a b c d : BitVec 64) :
    ((wordAddCarryHOL a b 0#64).2+(wordAddCarryHOL c d 0#64).2).toNat=
      (wordAddCarryHOL a b 0#64).2.toNat+(wordAddCarryHOL c d 0#64).2.toNat := by
  have first:=carry_flag_bound a b
  have second:=carry_flag_bound c d
  rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by omega)]

def scalarLow (a : Input.RlpWrite.U256Value.Words) (b : BitVec 64) : Input.RlpWrite.U256Value.Words:=
  fun index=>if index.val=0 then (Mul64.parts (a 0) b).1 else if index.val=1 then (scalarFirst a b).1
    else if index.val=2 then (scalarSecond a b).1 else (scalarThird a b).1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- All six actual accumulation carries give the exact full natural
product, before the Taylor overflow guard discards its high limbs. -/
theorem scalar_product (a : Input.RlpWrite.U256Value.Words) (b : BitVec 64) :
    U256Zero.number (scalarLow a b)+2^256*(scalarFourth a b).1.toNat+2^320*(scalarFourth a b).2.toNat=
      U256Zero.number a*b.toNat := by
  have p0:=Mul64.parts_product (a 0) b
  have p1:=Mul64.parts_product (a 1) b
  have p2:=Mul64.parts_product (a 2) b
  have p3:=Mul64.parts_product (a 3) b
  have c1:=Mul64.carry_number (Mul64.parts (a 0) b).2 (Mul64.parts (a 1) b).1
  have c2:=Mul64.carry_number (scalarFirst a b).2 (Mul64.parts (a 1) b).2
  have c3:=Mul64.carry_number (scalarSecondHigh a b).1 (Mul64.parts (a 2) b).1
  have c4:=Mul64.carry_number ((scalarSecondHigh a b).2+(scalarSecond a b).2) (Mul64.parts (a 2) b).2
  have c5:=Mul64.carry_number (scalarThirdHigh a b).1 (Mul64.parts (a 3) b).1
  have c6:=Mul64.carry_number ((scalarThirdHigh a b).2+(scalarThird a b).2) (Mul64.parts (a 3) b).2
  have flags2:=carry_flags_number (scalarFirst a b).2 (Mul64.parts (a 1) b).2
    (scalarSecondHigh a b).1 (Mul64.parts (a 2) b).1
  have flags3:=carry_flags_number ((scalarSecondHigh a b).2+(scalarSecond a b).2) (Mul64.parts (a 2) b).2
    (scalarThirdHigh a b).1 (Mul64.parts (a 3) b).1
  change (scalarFirst a b).1.toNat+2^64*(scalarFirst a b).2.toNat=_ at c1
  change (scalarSecondHigh a b).1.toNat+2^64*(scalarSecondHigh a b).2.toNat=_ at c2
  change (scalarSecond a b).1.toNat+2^64*(scalarSecond a b).2.toNat=_ at c3
  change (scalarThirdHigh a b).1.toNat+2^64*(scalarThirdHigh a b).2.toNat=_ at c4
  change (scalarThird a b).1.toNat+2^64*(scalarThird a b).2.toNat=_ at c5
  change (scalarFourth a b).1.toNat+2^64*(scalarFourth a b).2.toNat=_ at c6
  change ((scalarSecondHigh a b).2+(scalarSecond a b).2).toNat=(scalarSecondHigh a b).2.toNat+(scalarSecond a b).2.toNat at flags2
  change ((scalarThirdHigh a b).2+(scalarThird a b).2).toNat=(scalarThirdHigh a b).2.toNat+(scalarThird a b).2.toNat at flags3
  rw [flags2] at c4
  rw [flags3] at c6
  have expanded : U256Zero.number a*b.toNat=
      (a 0).toNat*b.toNat+2^64*((a 1).toNat*b.toNat)+2^128*((a 2).toNat*b.toNat)+2^192*((a 3).toNat*b.toNat) := by
    unfold U256Zero.number
    ring
  rw [←p0,←p1,←p2,←p3] at expanded
  change (Mul64.parts (a 0) b).1.toNat+2^64*(scalarFirst a b).1.toNat+2^128*(scalarSecond a b).1.toNat+
    2^192*(scalarThird a b).1.toNat+2^256*(scalarFourth a b).1.toNat+2^320*(scalarFourth a b).2.toNat=_
  omega

/-- The actual high-limb OR test is zero precisely when the product fits
in the four low limbs. -/
theorem scalar_overflow (a : Input.RlpWrite.U256Value.Words) (b : BitVec 64) :
    (scalarFourth a b).1 ||| (scalarFourth a b).2=0#64 ↔ U256Zero.number a*b.toNat<2^256 := by
  have product:=scalar_product a b
  have lowBound:=U256Zero.number_lt (scalarLow a b)
  rw [BitVec.or_eq_zero_iff]
  constructor
  · rintro ⟨first,second⟩
    simp only [first,second,BitVec.toNat_zero,Nat.mul_zero,Nat.add_zero] at product
    omega
  · intro small
    have first : (scalarFourth a b).1.toNat=0:=by omega
    have second : (scalarFourth a b).2.toNat=0:=by omega
    exact ⟨BitVec.eq_of_toNat_eq first,BitVec.eq_of_toNat_eq second⟩

theorem scalar_low_product (a : Input.RlpWrite.U256Value.Words) (b : BitVec 64)
    (fits : (scalarFourth a b).1 ||| (scalarFourth a b).2=0#64) :
    U256Zero.number (scalarLow a b)=U256Zero.number a*b.toNat := by
  have product:=scalar_product a b
  obtain ⟨first,second⟩:=BitVec.or_eq_zero_iff.mp fits
  simpa only [first,second,BitVec.toNat_zero,Nat.mul_zero,Nat.add_zero] using product

end InitECandidate.Solver.GasBudget.U256Multiply

#print axioms InitECandidate.Solver.GasBudget.U256Multiply.scalar_product
#print axioms InitECandidate.Solver.GasBudget.U256Multiply.scalar_overflow
#print axioms InitECandidate.Solver.GasBudget.U256Multiply.scalar_low_product


namespace InitECandidate.Solver.GasBudget.Mul64
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual normal results derive both their value and the source funding;
no successful future callee execution is supplied as an entry premise. -/
def NormalResult (source : PanSemStateFiniteExact 64 Guest.HostMemory) (program : ProgHOL 64)
    (expected : ValueHOL 64) (paid : Nat) : Prop:=
  ∀ post returned,evaluateHOLFiniteState source program=(some (.returned returned),post)→
    paid≤source.clock ∧ returned=expected ∧
      emptyLocalsHOLFinite post=emptyLocalsHOLFinite {source with clock:=source.clock-paid}

theorem value_zero_right (a : BitVec 64) : value a 0#64=.rStruct [.val (.word 0#64),.val (.word 0#64)] := by
  have product:=parts_product a 0#64
  simp only [BitVec.toNat_zero,Nat.mul_zero] at product
  have low : (parts a 0#64).1=0#64:=BitVec.eq_of_toNat_eq (by change (parts a 0#64).1.toNat=0;omega)
  have high : (parts a 0#64).2=0#64:=BitVec.eq_of_toNat_eq (by change (parts a 0#64).2.toNat=0;omega)
  simp only [value,low,high]

theorem scoped_normal_result (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (expected : ValueHOL 64) (paid : Nat)
    (installed : Input.OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word a),.val (.word b)])
    (next : NormalResult (setVarHOLFinite (ofString name) (value a b) {source with clock:=source.clock-1}) continuation expected paid) :
    NormalResult source (.decCall (ofString name) (.comb [.one,.one]) (ofString "mul64x64") arguments continuation) expected (paid+1) := by
  intro post returned normal
  obtain ⟨callee,called,aLocal,bLocal⟩:=environment source.code.lookup a b (current_code source.code installed)
  have funded:=(Input.CallNormal.scoped_normal source post name (.comb [.one,.one]) (ofString "mul64x64") arguments _
    body continuation callee (.comb [.one,.one]) args called returned normal).1
  rw [call_execute source a b name arguments continuation installed args funded] at normal
  let canonical:=setVarHOLFinite (ofString name) (value a b) {source with clock:=source.clock-1}
  let output:=evaluateHOLFiniteState canonical continuation
  change (output.1,restore source name output.2)=(some (.returned returned),post) at normal
  have resumed : evaluateHOLFiniteState canonical continuation=(some (.returned returned),output.2):=by
    apply Prod.ext
    · change output.1=some (.returned returned)
      exact congrArg Prod.fst normal
    · rfl
  obtain ⟨enough,result,frame⟩:=next output.2 returned resumed
  have more : paid≤source.clock-1:=enough
  refine ⟨by omega,result,?_⟩
  have postEq : restore source name output.2=post:=congrArg Prod.snd normal
  rw [←postEq]
  change emptyLocalsHOLFinite output.2=emptyLocalsHOLFinite {source with clock:=source.clock-(paid+1)}
  change emptyLocalsHOLFinite output.2=emptyLocalsHOLFinite {source with clock:=source.clock-1-paid} at frame
  have clockEq : source.clock-1-paid=source.clock-(paid+1):=by omega
  simpa only [clockEq] using frame

end InitECandidate.Solver.GasBudget.Mul64

#print axioms InitECandidate.Solver.GasBudget.Mul64.value_zero_right
#print axioms InitECandidate.Solver.GasBudget.Mul64.scoped_normal_result

namespace InitECandidate.Solver.GasBudget.U256Multiply
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxRecDepth 10000 in
theorem full_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "u256_mul_full")=some ([(ofString "a",Input.RlpWrite.U256Value.tupleShape),
      (ofString "b",Input.RlpWrite.U256Value.tupleShape)],fullBody,.comb [.one,.one,.one,.one,.one,.one,.one,.one]) := by
  have known:=ArithmeticEffects.current_environment code installed .u256_mul_full
  simpa only [ArithmeticEffects.Kind.name,ArithmeticEffects.Kind.signature,ArithmeticEffects.Kind.original,
    fullBody,ArithmeticEffects.Kind.body,Input.RlpWrite.U256Value.tupleShape,Guest.guestFn_u256_mul_full,shapeToHOL,List.map_cons,List.map_nil] using known

set_option maxRecDepth 10000 in
theorem full_shape : fullBody=
    (.decCall (ofString "p00") (.comb [.one,.one]) (ofString "mul64x64") [.rfield 0 (localVar "a"),.rfield 0 (localVar "b")]
    (.decCall (ofString "p01") (.comb [.one,.one]) (ofString "mul64x64") [.rfield 0 (localVar "a"),.rfield 1 (localVar "b")]
    (.decCall (ofString "p10") (.comb [.one,.one]) (ofString "mul64x64") [.rfield 1 (localVar "a"),.rfield 0 (localVar "b")]
    (.decCall (ofString "p02") (.comb [.one,.one]) (ofString "mul64x64") [.rfield 0 (localVar "a"),.rfield 2 (localVar "b")]
    (.decCall (ofString "p11") (.comb [.one,.one]) (ofString "mul64x64") [.rfield 1 (localVar "a"),.rfield 1 (localVar "b")]
    (.decCall (ofString "p20") (.comb [.one,.one]) (ofString "mul64x64") [.rfield 2 (localVar "a"),.rfield 0 (localVar "b")]
    (.decCall (ofString "p03") (.comb [.one,.one]) (ofString "mul64x64") [.rfield 0 (localVar "a"),.rfield 3 (localVar "b")]
    (.decCall (ofString "p12") (.comb [.one,.one]) (ofString "mul64x64") [.rfield 1 (localVar "a"),.rfield 2 (localVar "b")]
    (.decCall (ofString "p21") (.comb [.one,.one]) (ofString "mul64x64") [.rfield 2 (localVar "a"),.rfield 1 (localVar "b")]
    (.decCall (ofString "p30") (.comb [.one,.one]) (ofString "mul64x64") [.rfield 3 (localVar "a"),.rfield 0 (localVar "b")]
    (.decCall (ofString "p13") (.comb [.one,.one]) (ofString "mul64x64") [.rfield 1 (localVar "a"),.rfield 3 (localVar "b")]
    (.decCall (ofString "p22") (.comb [.one,.one]) (ofString "mul64x64") [.rfield 2 (localVar "a"),.rfield 2 (localVar "b")]
    (.decCall (ofString "p31") (.comb [.one,.one]) (ofString "mul64x64") [.rfield 3 (localVar "a"),.rfield 1 (localVar "b")]
    (.decCall (ofString "p23") (.comb [.one,.one]) (ofString "mul64x64") [.rfield 2 (localVar "a"),.rfield 3 (localVar "b")]
    (.decCall (ofString "p32") (.comb [.one,.one]) (ofString "mul64x64") [.rfield 3 (localVar "a"),.rfield 2 (localVar "b")]
    (.decCall (ofString "p33") (.comb [.one,.one]) (ofString "mul64x64") [.rfield 3 (localVar "a"),.rfield 3 (localVar "b")]
    afterProducts)))))))))))))))) := by
  simp only [afterProducts,dropProductCalls,fullBody,ArithmeticEffects.Kind.body,ArithmeticEffects.Kind.signature,
    ArithmeticEffects.Kind.original,Guest.guestFn_u256_mul_full,progToHOL,expToHOL,shapeToHOL,localVar,List.map_cons,List.map_nil]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- Every actual normal full-width multiplication with a scalar right input
supplies the checked eight-limb product, clock funding and full frame. -/
theorem scalar_normal (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (a : Input.RlpWrite.U256Value.Words) (b : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (aLocal : source.locals.lookup (ofString "a")=some (Input.RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b")=some (Input.RlpWrite.U256Value.tuple (wordQuad b))) :
    Mul64.NormalResult source fullBody (scalarValue a b) 16 := by
  classical
  have aRead : source.locals.lookup (MlString.implode [97#8])=some (Input.RlpWrite.U256Value.tuple a):=aLocal
  have bRead : source.locals.lookup (MlString.implode [98#8])=some (.rStruct [.val (.word b),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)]):=bLocal
  rw [full_shape]
  refine Mul64.scoped_normal_result source (a 0) b "p00" _ _ _ 15 installed ?_ ?_
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,ofString,localVar,Input.RlpWrite.U256Value.tuple,aRead,bRead] <;> rfl
  generalize eqFull1 : setVarHOLFinite (ofString "p00") (Mul64.value (a 0) b) {source with clock:=source.clock-1}=full1
  have fullLookup1 (key : MlS) : full1.locals.lookup key=
    (if ofString "p00"==key then some (Mul64.value (a 0) b) else source.locals.lookup key):=by
    rw [←eqFull1]
    rfl
  have installedFull1 : Input.OriginalCode.Installed full1.code:=by
    rw [←eqFull1]
    exact installed
  refine Mul64.scoped_normal_result full1 (a 0) 0#64 "p01" _ _ _ 14 installedFull1 ?_ ?_
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,ofString,localVar,Input.RlpWrite.U256Value.tuple,fullLookup1,aRead,bRead] <;> rfl
  generalize eqFull2 : setVarHOLFinite (ofString "p01") (Mul64.value (a 0) 0#64) {full1 with clock:=full1.clock-1}=full2
  have fullLookup2 (key : MlS) : full2.locals.lookup key=
    (if ofString "p01"==key then some (Mul64.value (a 0) 0#64) else full1.locals.lookup key):=by
    rw [←eqFull2]
    rfl
  have installedFull2 : Input.OriginalCode.Installed full2.code:=by
    rw [←eqFull2]
    exact installedFull1
  refine Mul64.scoped_normal_result full2 (a 1) b "p10" _ _ _ 13 installedFull2 ?_ ?_
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,ofString,localVar,Input.RlpWrite.U256Value.tuple,fullLookup2,fullLookup1,aRead,bRead] <;> rfl
  generalize eqFull3 : setVarHOLFinite (ofString "p10") (Mul64.value (a 1) b) {full2 with clock:=full2.clock-1}=full3
  have fullLookup3 (key : MlS) : full3.locals.lookup key=
    (if ofString "p10"==key then some (Mul64.value (a 1) b) else full2.locals.lookup key):=by
    rw [←eqFull3]
    rfl
  have installedFull3 : Input.OriginalCode.Installed full3.code:=by
    rw [←eqFull3]
    exact installedFull2
  refine Mul64.scoped_normal_result full3 (a 0) 0#64 "p02" _ _ _ 12 installedFull3 ?_ ?_
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,ofString,localVar,Input.RlpWrite.U256Value.tuple,fullLookup3,fullLookup2,fullLookup1,aRead,bRead] <;> rfl
  generalize eqFull4 : setVarHOLFinite (ofString "p02") (Mul64.value (a 0) 0#64) {full3 with clock:=full3.clock-1}=full4
  have fullLookup4 (key : MlS) : full4.locals.lookup key=
    (if ofString "p02"==key then some (Mul64.value (a 0) 0#64) else full3.locals.lookup key):=by
    rw [←eqFull4]
    rfl
  have installedFull4 : Input.OriginalCode.Installed full4.code:=by
    rw [←eqFull4]
    exact installedFull3
  refine Mul64.scoped_normal_result full4 (a 1) 0#64 "p11" _ _ _ 11 installedFull4 ?_ ?_
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,ofString,localVar,Input.RlpWrite.U256Value.tuple,fullLookup4,fullLookup3,fullLookup2,fullLookup1,aRead,bRead] <;> rfl
  generalize eqFull5 : setVarHOLFinite (ofString "p11") (Mul64.value (a 1) 0#64) {full4 with clock:=full4.clock-1}=full5
  have fullLookup5 (key : MlS) : full5.locals.lookup key=
    (if ofString "p11"==key then some (Mul64.value (a 1) 0#64) else full4.locals.lookup key):=by
    rw [←eqFull5]
    rfl
  have installedFull5 : Input.OriginalCode.Installed full5.code:=by
    rw [←eqFull5]
    exact installedFull4
  refine Mul64.scoped_normal_result full5 (a 2) b "p20" _ _ _ 10 installedFull5 ?_ ?_
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,ofString,localVar,Input.RlpWrite.U256Value.tuple,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1,aRead,bRead] <;> rfl
  generalize eqFull6 : setVarHOLFinite (ofString "p20") (Mul64.value (a 2) b) {full5 with clock:=full5.clock-1}=full6
  have fullLookup6 (key : MlS) : full6.locals.lookup key=
    (if ofString "p20"==key then some (Mul64.value (a 2) b) else full5.locals.lookup key):=by
    rw [←eqFull6]
    rfl
  have installedFull6 : Input.OriginalCode.Installed full6.code:=by
    rw [←eqFull6]
    exact installedFull5
  refine Mul64.scoped_normal_result full6 (a 0) 0#64 "p03" _ _ _ 9 installedFull6 ?_ ?_
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,ofString,localVar,Input.RlpWrite.U256Value.tuple,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1,aRead,bRead] <;> rfl
  generalize eqFull7 : setVarHOLFinite (ofString "p03") (Mul64.value (a 0) 0#64) {full6 with clock:=full6.clock-1}=full7
  have fullLookup7 (key : MlS) : full7.locals.lookup key=
    (if ofString "p03"==key then some (Mul64.value (a 0) 0#64) else full6.locals.lookup key):=by
    rw [←eqFull7]
    rfl
  have installedFull7 : Input.OriginalCode.Installed full7.code:=by
    rw [←eqFull7]
    exact installedFull6
  refine Mul64.scoped_normal_result full7 (a 1) 0#64 "p12" _ _ _ 8 installedFull7 ?_ ?_
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,ofString,localVar,Input.RlpWrite.U256Value.tuple,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1,aRead,bRead] <;> rfl
  generalize eqFull8 : setVarHOLFinite (ofString "p12") (Mul64.value (a 1) 0#64) {full7 with clock:=full7.clock-1}=full8
  have fullLookup8 (key : MlS) : full8.locals.lookup key=
    (if ofString "p12"==key then some (Mul64.value (a 1) 0#64) else full7.locals.lookup key):=by
    rw [←eqFull8]
    rfl
  have installedFull8 : Input.OriginalCode.Installed full8.code:=by
    rw [←eqFull8]
    exact installedFull7
  refine Mul64.scoped_normal_result full8 (a 2) 0#64 "p21" _ _ _ 7 installedFull8 ?_ ?_
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,ofString,localVar,Input.RlpWrite.U256Value.tuple,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1,aRead,bRead] <;> rfl
  generalize eqFull9 : setVarHOLFinite (ofString "p21") (Mul64.value (a 2) 0#64) {full8 with clock:=full8.clock-1}=full9
  have fullLookup9 (key : MlS) : full9.locals.lookup key=
    (if ofString "p21"==key then some (Mul64.value (a 2) 0#64) else full8.locals.lookup key):=by
    rw [←eqFull9]
    rfl
  have installedFull9 : Input.OriginalCode.Installed full9.code:=by
    rw [←eqFull9]
    exact installedFull8
  refine Mul64.scoped_normal_result full9 (a 3) b "p30" _ _ _ 6 installedFull9 ?_ ?_
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,ofString,localVar,Input.RlpWrite.U256Value.tuple,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1,aRead,bRead] <;> rfl
  generalize eqFull10 : setVarHOLFinite (ofString "p30") (Mul64.value (a 3) b) {full9 with clock:=full9.clock-1}=full10
  have fullLookup10 (key : MlS) : full10.locals.lookup key=
    (if ofString "p30"==key then some (Mul64.value (a 3) b) else full9.locals.lookup key):=by
    rw [←eqFull10]
    rfl
  have installedFull10 : Input.OriginalCode.Installed full10.code:=by
    rw [←eqFull10]
    exact installedFull9
  refine Mul64.scoped_normal_result full10 (a 1) 0#64 "p13" _ _ _ 5 installedFull10 ?_ ?_
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,ofString,localVar,Input.RlpWrite.U256Value.tuple,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1,aRead,bRead] <;> rfl
  generalize eqFull11 : setVarHOLFinite (ofString "p13") (Mul64.value (a 1) 0#64) {full10 with clock:=full10.clock-1}=full11
  have fullLookup11 (key : MlS) : full11.locals.lookup key=
    (if ofString "p13"==key then some (Mul64.value (a 1) 0#64) else full10.locals.lookup key):=by
    rw [←eqFull11]
    rfl
  have installedFull11 : Input.OriginalCode.Installed full11.code:=by
    rw [←eqFull11]
    exact installedFull10
  refine Mul64.scoped_normal_result full11 (a 2) 0#64 "p22" _ _ _ 4 installedFull11 ?_ ?_
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,ofString,localVar,Input.RlpWrite.U256Value.tuple,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1,aRead,bRead] <;> rfl
  generalize eqFull12 : setVarHOLFinite (ofString "p22") (Mul64.value (a 2) 0#64) {full11 with clock:=full11.clock-1}=full12
  have fullLookup12 (key : MlS) : full12.locals.lookup key=
    (if ofString "p22"==key then some (Mul64.value (a 2) 0#64) else full11.locals.lookup key):=by
    rw [←eqFull12]
    rfl
  have installedFull12 : Input.OriginalCode.Installed full12.code:=by
    rw [←eqFull12]
    exact installedFull11
  refine Mul64.scoped_normal_result full12 (a 3) 0#64 "p31" _ _ _ 3 installedFull12 ?_ ?_
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,ofString,localVar,Input.RlpWrite.U256Value.tuple,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1,aRead,bRead] <;> rfl
  generalize eqFull13 : setVarHOLFinite (ofString "p31") (Mul64.value (a 3) 0#64) {full12 with clock:=full12.clock-1}=full13
  have fullLookup13 (key : MlS) : full13.locals.lookup key=
    (if ofString "p31"==key then some (Mul64.value (a 3) 0#64) else full12.locals.lookup key):=by
    rw [←eqFull13]
    rfl
  have installedFull13 : Input.OriginalCode.Installed full13.code:=by
    rw [←eqFull13]
    exact installedFull12
  refine Mul64.scoped_normal_result full13 (a 2) 0#64 "p23" _ _ _ 2 installedFull13 ?_ ?_
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,ofString,localVar,Input.RlpWrite.U256Value.tuple,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1,aRead,bRead] <;> rfl
  generalize eqFull14 : setVarHOLFinite (ofString "p23") (Mul64.value (a 2) 0#64) {full13 with clock:=full13.clock-1}=full14
  have fullLookup14 (key : MlS) : full14.locals.lookup key=
    (if ofString "p23"==key then some (Mul64.value (a 2) 0#64) else full13.locals.lookup key):=by
    rw [←eqFull14]
    rfl
  have installedFull14 : Input.OriginalCode.Installed full14.code:=by
    rw [←eqFull14]
    exact installedFull13
  refine Mul64.scoped_normal_result full14 (a 3) 0#64 "p32" _ _ _ 1 installedFull14 ?_ ?_
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,ofString,localVar,Input.RlpWrite.U256Value.tuple,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1,aRead,bRead] <;> rfl
  generalize eqFull15 : setVarHOLFinite (ofString "p32") (Mul64.value (a 3) 0#64) {full14 with clock:=full14.clock-1}=full15
  have fullLookup15 (key : MlS) : full15.locals.lookup key=
    (if ofString "p32"==key then some (Mul64.value (a 3) 0#64) else full14.locals.lookup key):=by
    rw [←eqFull15]
    rfl
  have installedFull15 : Input.OriginalCode.Installed full15.code:=by
    rw [←eqFull15]
    exact installedFull14
  refine Mul64.scoped_normal_result full15 (a 3) 0#64 "p33" _ _ _ 0 installedFull15 ?_ ?_
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,ofString,localVar,Input.RlpWrite.U256Value.tuple,fullLookup15,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1,aRead,bRead] <;> rfl
  generalize eqFull16 : setVarHOLFinite (ofString "p33") (Mul64.value (a 3) 0#64) {full15 with clock:=full15.clock-1}=full16
  have fullLookup16 (key : MlS) : full16.locals.lookup key=
    (if ofString "p33"==key then some (Mul64.value (a 3) 0#64) else full15.locals.lookup key):=by
    rw [←eqFull16]
    rfl
  have installedFull16 : Input.OriginalCode.Installed full16.code:=by
    rw [←eqFull16]
    exact installedFull15
  have actual00 : full16.locals.lookup (ofString "p00")=some (Mul64.value (a 0) b):=by
    simp [ofString,Mul64.value_zero_right,fullLookup16,fullLookup15,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1]
  have actual01 : full16.locals.lookup (ofString "p01")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=by
    simp [ofString,Mul64.value_zero_right,fullLookup16,fullLookup15,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1]
  have actual02 : full16.locals.lookup (ofString "p02")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=by
    simp [ofString,Mul64.value_zero_right,fullLookup16,fullLookup15,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1]
  have actual03 : full16.locals.lookup (ofString "p03")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=by
    simp [ofString,Mul64.value_zero_right,fullLookup16,fullLookup15,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1]
  have actual10 : full16.locals.lookup (ofString "p10")=some (Mul64.value (a 1) b):=by
    simp [ofString,Mul64.value_zero_right,fullLookup16,fullLookup15,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1]
  have actual11 : full16.locals.lookup (ofString "p11")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=by
    simp [ofString,Mul64.value_zero_right,fullLookup16,fullLookup15,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1]
  have actual12 : full16.locals.lookup (ofString "p12")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=by
    simp [ofString,Mul64.value_zero_right,fullLookup16,fullLookup15,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1]
  have actual13 : full16.locals.lookup (ofString "p13")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=by
    simp [ofString,Mul64.value_zero_right,fullLookup16,fullLookup15,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1]
  have actual20 : full16.locals.lookup (ofString "p20")=some (Mul64.value (a 2) b):=by
    simp [ofString,Mul64.value_zero_right,fullLookup16,fullLookup15,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1]
  have actual21 : full16.locals.lookup (ofString "p21")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=by
    simp [ofString,Mul64.value_zero_right,fullLookup16,fullLookup15,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1]
  have actual22 : full16.locals.lookup (ofString "p22")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=by
    simp [ofString,Mul64.value_zero_right,fullLookup16,fullLookup15,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1]
  have actual23 : full16.locals.lookup (ofString "p23")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=by
    simp [ofString,Mul64.value_zero_right,fullLookup16,fullLookup15,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1]
  have actual30 : full16.locals.lookup (ofString "p30")=some (Mul64.value (a 3) b):=by
    simp [ofString,Mul64.value_zero_right,fullLookup16,fullLookup15,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1]
  have actual31 : full16.locals.lookup (ofString "p31")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=by
    simp [ofString,Mul64.value_zero_right,fullLookup16,fullLookup15,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1]
  have actual32 : full16.locals.lookup (ofString "p32")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=by
    simp [ofString,Mul64.value_zero_right,fullLookup16,fullLookup15,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1]
  have actual33 : full16.locals.lookup (ofString "p33")=some (.rStruct [.val (.word 0#64),.val (.word 0#64)]):=by
    simp [ofString,Mul64.value_zero_right,fullLookup16,fullLookup15,fullLookup14,fullLookup13,fullLookup12,fullLookup11,fullLookup10,fullLookup9,fullLookup8,fullLookup7,fullLookup6,fullLookup5,fullLookup4,fullLookup3,fullLookup2,fullLookup1]
  obtain ⟨target,run,frame⟩:=scalar_tail full16 a b actual00 actual01 actual02 actual03 actual10 actual11 actual12 actual13 actual20 actual21 actual22 actual23 actual30 actual31 actual32 actual33
  intro post returned normal
  have same:=normal.symm.trans run
  have result : returned=scalarValue a b:=by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using congrArg Prod.fst same
  have postEq : post=target:=congrArg Prod.snd same
  exact ⟨Nat.zero_le _,result,postEq ▸ frame⟩

end InitECandidate.Solver.GasBudget.U256Multiply

#print axioms InitECandidate.Solver.GasBudget.U256Multiply.full_code
#print axioms InitECandidate.Solver.GasBudget.U256Multiply.full_shape
#print axioms InitECandidate.Solver.GasBudget.U256Multiply.scalar_normal

namespace InitECandidate.Solver.GasBudget.U256Multiply
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual callee return through the genuine current two-quadruple ABI.
The result, seventeen caller ticks and canonical resumption are derived
from the same successful child run. -/
theorem scalar_resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (a : Input.RlpWrite.U256Value.Words) (b : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "u256_mul_full")
      [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple (wordQuad b)]=some (actual,callee,shape))
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual=(some (.returned returned),target)) :
    returned=scalarValue a b ∧ 17≤source.clock ∧
      Input.CallNormal.continuationEntry source target name returned=
        setVarHOLFinite (ofString name) (scalarValue a b) {source with clock:=source.clock-17} := by
  obtain ⟨expected,lookup,aCell,bCell⟩:=Input.RlpWrite.U256Value.pair_environment source.code.lookup
    (ofString "u256_mul_full") fullBody (.comb [.one,.one,.one,.one,.one,.one,.one,.one]) a (wordQuad b)
    (full_code source.code installed)
  have same:=Option.some.inj (called.symm.trans lookup)
  have bodyEq : actual=fullBody:=congrArg Prod.fst same
  have calleeEq : callee=expected:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  rw [←calleeEq] at aCell bCell
  rw [bodyEq] at run
  obtain ⟨funded,result,frame⟩:=scalar_normal (callEntryStateHOLFinite source callee) a b installed aCell bCell target returned run
  have more : 16≤source.clock-1:=funded
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  have canonical : {target with locals:=source.locals}={source with clock:=source.clock-17} := by
    simpa only [emptyLocalsHOLFinite,callEntryStateHOLFinite,Nat.sub_sub] using callerFrame
  exact ⟨result,by omega,by simp only [Input.CallNormal.continuationEntry,result,canonical]⟩

end InitECandidate.Solver.GasBudget.U256Multiply

#print axioms InitECandidate.Solver.GasBudget.U256Multiply.scalar_resume
