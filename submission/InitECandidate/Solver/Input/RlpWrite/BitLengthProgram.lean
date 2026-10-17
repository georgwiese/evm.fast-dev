import InitECandidate.Solver.Input.RlpWrite.BytesWriteCall

namespace InitECandidate.Solver.Input.RlpWrite.BitLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_bit_length64 with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "x",.one)]
def shifted (amount : Nat) : ExpHOL 64 := .shift .lsr (localVar "x") (.const (BitVec.ofNat 64 amount))
def test (amount : Nat) : ExpHOL 64 := .cmp .notEqual (shifted amount) (.const 0#64)
def addition (amount : Nat) : ExpHOL 64 := .op .add [localVar "n",.const (BitVec.ofNat 64 amount)]
def active (amount : Nat) : ProgHOL 64 := .seq (.assign .local (ofString "n") (addition amount)) (.assign .local (ofString "x") (shifted amount))
def stage (amount : Nat) : ProgHOL 64 := .ite (test amount) (active amount) .skip
def stages : List Nat→ProgHOL 64
  | []=>.return (.op .add [localVar "n",localVar "x"])
  | amount::rest=>.seq (stage amount) (stages rest)

theorem body_shape : body=.dec (ofString "n") .one (.const 0#64) (stages [32,16,8,4,2,1]) := by
  simp only [body,Guest.guestFn_bit_length64,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    stages,stage,test,active,shifted,addition,localVar]

theorem stage_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64) (count amount : Nat)
    (amountSmall : amount<64) (valueBound : value.toNat<2^(2*amount))
    (x : source.locals.lookup (ofString "x")=some (.val (.word value)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))) :
    ∃ target nextValue nextCount,nextCount≤count+amount ∧ nextValue.toNat<2^amount ∧
      evaluateHOLFiniteState source (stage amount)=(none,target) ∧ target={source with locals:=target.locals} ∧
      target.locals.lookup (ofString "x")=some (.val (.word nextValue)) ∧
      target.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 nextCount))) := by
  classical
  have amountNumber : (BitVec.ofNat 64 amount).toNat=amount := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have shiftRead : eval source (shifted amount)=some (.val (.word (value >>> amount))) := by
    simp [eval,shifted,localVar,evalHOLExact,toExact,x,wordShiftHOL,amountNumber,amountSmall]
  have testRead : eval source (test amount)=some (.val (.word (if value>>>amount=0#64 then 0#64 else 1#64))) := by
    simp only [eval] at shiftRead ⊢
    rw [test,evalHOLExact,shiftRead]
    simp [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have positive : 0<2^amount:=Nat.two_pow_pos amount
  by_cases zero : value>>>amount=0#64
  · have native:=congrArg BitVec.toNat zero
    rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow] at native
    have bound : value.toNat<2^amount := by
      have quotient : value.toNat/2^amount<1 := by change value.toNat/2^amount=0 at native; omega
      have raw:=(Nat.div_lt_iff_lt_mul positive).mp quotient
      simpa using raw
    refine ⟨source,value,count,by omega,bound,?_,rfl,x,n⟩
    simp only [eval] at testRead
    rw [stage,evaluateHOLFiniteState_ite,testRead]
    simp [zero]
  · have bound : (value>>>amount).toNat<2^amount := by
      rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
      apply (Nat.div_lt_iff_lt_mul positive).mpr
      simpa only [two_mul,Nat.pow_add] using valueBound
    have addRead : eval source (addition amount)=some (.val (.word (BitVec.ofNat 64 (count+amount)))) := by
      simp [eval,addition,localVar,evalHOLExact,evalListHOLExact,toExact,n,valueIsWord,valueWord,wordOpHOL,wordOp,←BitVec.ofNat_add]
    let added:=bind source "n" (BitVec.ofNat 64 (count+amount))
    have addRun:=WitnessRadix.StateSteps.assign_execute source "n" (addition amount) _ _ n addRead
    have xAdded : added.locals.lookup (ofString "x")=some (.val (.word value)):=
      (bind_lookup_other _ "n" "x" _ (by decide)).trans x
    have shiftedRead : eval added (shifted amount)=some (.val (.word (value>>>amount))) := by
      simp [eval,shifted,localVar,evalHOLExact,toExact,xAdded,wordShiftHOL,amountNumber,amountSmall]
    have shiftRun:=WitnessRadix.StateSteps.assign_execute added "x" (shifted amount) _ _ xAdded shiftedRead
    let target:=bind added "x" (value>>>amount)
    have activeRun : evaluateHOLFiniteState source (active amount)=(none,target) := by
      rw [active,WitnessRadix.StateSteps.next_sequence source added _ _ addRun (Nat.le_refl _)]
      exact shiftRun
    refine ⟨target,value>>>amount,count+amount,by omega,bound,?_,rfl,bind_lookup_same _ _ _,?_⟩
    · simp only [eval] at testRead
      rw [stage,evaluateHOLFiniteState_ite,testRead]
      simpa [zero] using activeRun
    · exact (bind_lookup_other _ "x" "n" _ (by decide)).trans (bind_lookup_same _ _ _)

end InitECandidate.Solver.Input.RlpWrite.BitLength

#print axioms InitECandidate.Solver.Input.RlpWrite.BitLength.body_shape
#print axioms InitECandidate.Solver.Input.RlpWrite.BitLength.stage_execute
