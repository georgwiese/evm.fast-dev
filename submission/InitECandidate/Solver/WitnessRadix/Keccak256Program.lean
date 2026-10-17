import InitECandidate.Solver.WitnessRadix.KeccakAbsorbCall
import InitECandidate.Solver.WitnessRadix.ZeroCall

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_keccak256 with | .function fn => progToHOL fn.body | _ => .skip
def condition : ExpHOL 64 := .cmp .notLower (localVar "n") (addConst (localVar "i") 136#64)
def blockArguments : List (ExpHOL 64) := [localVar "stp", .op .add [localVar "p", localVar "i"]]
def blockBody : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "keccak_absorb_block") blockArguments) (CopyBytes.increment 136#64)
def blocks : ProgHOL 64 := .while condition blockBody
def afterBlocks : ProgHOL 64 := match body with
  | .dec _ _ _ (.seq _ (.dec _ _ _ (.seq _ rest))) => rest
  | _ => .skip

theorem body_shape : body = .dec (ofString "stp") .one (.var .global (ofString "keccak_st"))
    (.seq (.call (some (none,none)) (ofString "memzero") [localVar "stp",.const 200#64])
      (.dec (ofString "i") .one (.const 0#64) (.seq blocks afterBlocks))) := by
  simp only [body,Guest.guestFn_keccak256,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    blocks,condition,blockBody,blockArguments,CopyBytes.increment,localVar,addConst,afterBlocks]
  rfl

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.body_shape
