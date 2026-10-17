import InitECandidate.Solver.GasBudget.AddExact
import InitECandidate.Solver.GasBudget.Calls

namespace InitECandidate.Solver.GasBudget.StateCharge
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_charge_state_gas with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "amount",.one)]
def returnZero : ProgHOL 64 := .return (.const 0#64)
def firstTest : ExpHOL 64 := .cmp .notLower (localVar "sgl") (localVar "amount")
def remainderExpression : ExpHOL 64 := .op .sub [localVar "amount",localVar "sgl"]
def firstBranch : ProgHOL 64 := .seq (.store (frameAddress 72#64) (.op .sub [localVar "sgl",localVar "amount"])) returnZero
def spillGasExpression : ExpHOL 64 := .op .sub [localVar "gl",localVar "rem"]
def spillUsedExpression : ExpHOL 64 := .op .add [frameLoad 192#64,localVar "rem"]
def spillTail : ProgHOL 64 := .seq (.store (frameAddress 72#64) (.const 0#64))
  (.seq (.store (frameAddress 64#64) spillGasExpression) (.seq (.store (frameAddress 192#64) spillUsedExpression) returnZero))
def spillCode : ProgHOL 64 := .dec (ofString "rem") .one remainderExpression spillTail
def totalTest : ExpHOL 64 := .cmp .notLower (localVar "tot") (localVar "amount")
def failure : ProgHOL 64 := .seq (.raise (ofString "EvmErr") (.const 4#64)) returnZero
def afterTotal : ProgHOL 64 := .seq (.ite totalTest spillCode .skip) failure
def afterPools : ProgHOL 64 := .seq (.ite firstTest firstBranch .skip)
  (.decCall (ofString "tot") .one (ofString "add_sat") [localVar "sgl",localVar "gl"] afterTotal)
def bindings : List (String×ExpHOL 64) := [("sgl",frameLoad 72#64),("gl",frameLoad 64#64)]

theorem body_shape : body=WitnessRadix.BuildEntry.declarations bindings afterPools := by
  simp only [body,Guest.guestFn_charge_state_gas,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    bindings,WitnessRadix.BuildEntry.declarations,afterPools,firstTest,firstBranch,returnZero,afterTotal,totalTest,spillCode,
    remainderExpression,spillTail,spillGasExpression,spillUsedExpression,failure,frameLoad,frameAddress,localVar]

structure Pools (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas state spill : BitVec 64) : Prop where
  ev : source.globals.lookup (ofString "ev")=some (.val (.word frame))
  mapped : ∀ offset∈([64,72,192] : List Nat),source.memaddrs (frame+BitVec.ofNat 64 offset)
  gas : source.memory (frame+64#64)=.word gas
  state : source.memory (frame+72#64)=.word state
  spill : source.memory (frame+192#64)=.word spill

def poolWrites (frame gas state spill amount : BitVec 64) : List (BitVec 64×BitVec 64) :=
  if amount≤state then [(frame+72#64,state-amount)] else
  [(frame+72#64,0#64),(frame+64#64,gas-(amount-state)),(frame+192#64,spill+(amount-state))]

end InitECandidate.Solver.GasBudget.StateCharge

#print axioms InitECandidate.Solver.GasBudget.StateCharge.body_shape
