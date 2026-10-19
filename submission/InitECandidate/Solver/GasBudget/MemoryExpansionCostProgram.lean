import InitECandidate.Solver.GasBudget.MemoryCostKnownCalls
import InitECandidate.Solver.GasBudget.Ceil32Arithmetic
import InitECandidate.Solver.GasBudget.FrameField

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.RlpWrite

def body := MemoryCostEffects.Kind.extend_memory_cost1.body
def pairValue (pair : BitVec 64 × BitVec 64) : ValueHOL 64 := .rStruct [.val (.word pair.1), .val (.word pair.2)]
def pairExpression (a b : BitVec 64) : ExpHOL 64 := .rstruct [.const a, .const b]
def returnZero : ProgHOL 64 := .return (pairExpression 0#64 0#64)
def returnMax : ProgHOL 64 := .return (pairExpression 18446744073709551615#64 0#64)
def maxGuard (name : String) : ProgHOL 64 := .ite (.cmp .equal (localVar name) (.const 18446744073709551615#64)) returnMax .skip
def zeroGuard : ProgHOL 64 := .ite (.cmp .notEqual (localVar "z") (.const 0#64)) returnZero .skip
def growthGuard : ProgHOL 64 := .ite (.cmp .notLower (localVar "before") (localVar "after")) returnZero .skip
def finish : ProgHOL 64 := .return (.rstruct [.op .sub [localVar "ca", localVar "cb"], .op .sub [localVar "after", localVar "before"]])
def afterCB : ProgHOL 64 := .seq (maxGuard "ca") finish
def afterCA : ProgHOL 64 := .decCall (ofString "cb") .one (ofString "memory_gas_cost") [localVar "before"] afterCB
def afterGrowth : ProgHOL 64 := .decCall (ofString "ca") .one (ofString "memory_gas_cost") [localVar "after"] afterCA
def afterAfter : ProgHOL 64 := .seq growthGuard afterGrowth
def afterBefore : ProgHOL 64 := .decCall (ofString "after") .one (ofString "ceil32") [localVar "endp"] afterAfter
def afterCurrent : ProgHOL 64 := .decCall (ofString "before") .one (ofString "ceil32") [localVar "cur"] afterBefore
def afterEnd : ProgHOL 64 := .seq (maxGuard "endp") (.dec (ofString "cur") .one (frameLoad 32#64) afterCurrent)
def afterN : ProgHOL 64 := .decCall (ofString "endp") .one (ofString "add_sat") [localVar "s", localVar "n"] afterEnd
def afterS : ProgHOL 64 := .decCall (ofString "n") .one (ofString "sat_word") [localVar "size"] afterN
def afterZero : ProgHOL 64 := .decCall (ofString "s") .one (ofString "sat_word") [localVar "start"] afterS
def afterZ : ProgHOL 64 := .seq zeroGuard afterZero

theorem body_shape : body = .decCall (ofString "z") .one (ofString "u256_is_zero") [localVar "size"] afterZ := by
  simp only [body, MemoryCostEffects.Kind.body, MemoryCostEffects.Kind.signature, MemoryCostEffects.Kind.original,
    Guest.guestFn_extend_memory_cost1, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none,
    afterZ, afterZero, afterS, afterN, afterEnd, afterCurrent, afterBefore, afterAfter, afterGrowth, afterCA, afterCB,
    zeroGuard, maxGuard, growthGuard, returnZero, returnMax, finish, pairExpression, localVar, frameLoad, frameAddress]

def finalPair (before after : BitVec 64) : BitVec 64 × BitVec 64 :=
  if MemoryGasCost.resultWord after = 18446744073709551615#64 then (18446744073709551615#64, 0#64)
  else (MemoryGasCost.resultWord after - MemoryGasCost.resultWord before, after - before)
def endPair (current endp : BitVec 64) : BitVec 64 × BitVec 64 :=
  if endp = 18446744073709551615#64 then (18446744073709551615#64, 0#64)
  else if Ceil32.resultWord endp ≤ Ceil32.resultWord current then (0#64, 0#64)
  else finalPair (Ceil32.resultWord current) (Ceil32.resultWord endp)
def resultPair (start size : U256Value.Words) (current : BitVec 64) : BitVec 64 × BitVec 64 :=
  if U256Zero.resultWord size ≠ 0#64 then (0#64, 0#64)
  else endPair current (SaturatingAdd.resultWord (SatWord.resultWord start) (SatWord.resultWord size))

structure View (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current : BitVec 64) : Prop where
  installed : Input.OriginalCode.Installed source.code
  ev : source.globals.lookup (ofString "ev") = some (.val (.word frame))
  mapped : source.memaddrs (frame + 32#64)
  cell : source.memory (frame + 32#64) = .word current

theorem View.after_erase {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame current : BitVec 64}
    (view : View source frame current) (fields : Input.LocalEffects.erase target = Input.LocalEffects.erase source) : View target frame current := by
  have code := congrArg PanSemStateFiniteExact.code fields
  have globals := congrArg PanSemStateFiniteExact.globals fields
  have mapped := congrArg PanSemStateFiniteExact.memaddrs fields
  have memory := congrArg PanSemStateFiniteExact.memory fields
  change target.code = source.code at code
  change target.globals = source.globals at globals
  change target.memaddrs = source.memaddrs at mapped
  change target.memory = source.memory at memory
  exact ⟨by rw [code]; exact view.installed, by rw [globals]; exact view.ev,
    by rw [mapped]; exact view.mapped, by rw [memory]; exact view.cell⟩

end InitECandidate.Solver.GasBudget.MemoryExpansionCost

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost.body_shape
#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost.View.after_erase
