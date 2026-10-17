import InitECandidate.Solver.Input.RlpLength.WithdrawalCall
import InitECandidate.Solver.Input.ScopeLookup

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_block_rlp_length with | .function fn=>progToHOL fn.body | _=>.skip
def loops : ProgHOL 64→List (ProgHOL 64)
  | code@(.while _ inner)=>code::loops inner
  | .seq first second=>loops first++loops second
  | .dec _ _ _ inner | .decCall _ _ _ _ inner=>loops inner
  | .ite _ first second=>loops first++loops second
  | _=>[]
def withdrawalLoop : ProgHOL 64 := ((loops body)[1]?).getD .skip
def loopTest : ExpHOL 64 := .cmp .less (localVar "i") (localVar "nwd")
def withdrawalBase : ExpHOL 64 := .load .one (.op .add [localVar "pl",.const 48#64])
def withdrawalArguments : List (ExpHOL 64) := [.op .add [withdrawalBase,.panop .mul [localVar "i",.const 44#64]]]
def sumExpression : ExpHOL 64 := .op .add [localVar "wl",localVar "wlen"]
def incrementExpression : ExpHOL 64 := .op .add [localVar "i",.const 1#64]
def afterLength : ProgHOL 64 := .seq (.assign .local (ofString "wl") sumExpression) (.assign .local (ofString "i") incrementExpression)
def loopBody : ProgHOL 64 := .decCall (ofString "wlen") .one (ofString "withdrawal_rlp_len") withdrawalArguments afterLength

theorem loop_shape : withdrawalLoop=.while loopTest loopBody := by
  simp only [withdrawalLoop,loops,body,Guest.guestFn_block_rlp_length,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    List.nil_append,List.cons_append,List.append_nil,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    loopTest,loopBody,withdrawalArguments,withdrawalBase,afterLength,sumExpression,incrementExpression,localVar]

def step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (paid index sum encoded : Nat) :=
  bind (bind {source with clock:=source.clock-1-paid} "wl" (BitVec.ofNat 64 (sum+encoded))) "i" (BitVec.ofNat 64 (index+1))

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.loop_shape
