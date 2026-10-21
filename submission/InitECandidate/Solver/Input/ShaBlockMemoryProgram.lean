import InitECandidate.Solver.Input.ShaBlockCounterCost

namespace InitECandidate.Solver.Input.ShaFixedCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def packedAddress : ExpHOL 64 := .op .add [.var .global (ofString "sha_accel"),.panop .mul [localVar "i",.const 8#64]]
def stateAddress : ExpHOL 64 := .op .add [localVar "stp",.panop .mul [localVar "i",.const 16#64]]
def stateAddressHi : ExpHOL 64 := .op .add [localVar "stp",.panop .mul [localVar "i",.const 16#64],.const 8#64]
def packedArguments : List (ExpHOL 64) := [
  .shift .lsr (.shift .lsl (localVar "lo") (.const 32#64)) (.const 32#64),
  .shift .lsl (.shift .lsr (.shift .lsl (localVar "hi") (.const 32#64)) (.const 32#64)) (.const 32#64)]
def firstMemoryTail : ProgHOL 64 := .seq (.store packedAddress (.op .or packedArguments)) increment

def stateLowValue : ExpHOL 64 := .shift .lsl (localVar "packed") (.const 32#64)
def secondMemoryTail : ProgHOL 64 := .seq (.store stateAddress (.shift .lsr stateLowValue (.const 32#64)))
  (.seq (.store stateAddressHi (.shift .lsr (localVar "packed") (.const 32#64))) increment)

set_option maxRecDepth 10000 in
theorem first_memory_shape : firstStep=.dec (ofString "lo") .one (.load .one stateAddress)
    (.dec (ofString "hi") .one (.load .one stateAddressHi) firstMemoryTail) := by
  simp only [firstStep,firstLoop,blockBody,BuildProgram.loops,Guest.guestFn_sha256_block,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_nil,List.getElem?_cons_zero,Option.getD_some,
    firstMemoryTail,packedAddress,stateAddress,stateAddressHi,packedArguments,increment,localVar]

set_option maxRecDepth 10000 in
theorem second_memory_shape : secondStep=.dec (ofString "packed") .one (.load .one packedAddress) secondMemoryTail := by
  simp only [secondStep,secondLoop,blockBody,BuildProgram.loops,Guest.guestFn_sha256_block,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_nil,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    secondMemoryTail,stateLowValue,packedAddress,stateAddress,stateAddressHi,increment,localVar]

end InitECandidate.Solver.Input.ShaFixedCost

#print axioms InitECandidate.Solver.Input.ShaFixedCost.first_memory_shape
#print axioms InitECandidate.Solver.Input.ShaFixedCost.second_memory_shape
