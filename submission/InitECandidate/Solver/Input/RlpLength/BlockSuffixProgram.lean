import InitECandidate.Solver.Input.RlpLength.BlockLoop
import InitECandidate.Solver.Input.RlpLength.ListHeaderAssign

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def loopTails : ProgHOL 64→List (ProgHOL 64)
  | .seq first second=>(match first with | .while _ _=>[second] | _=>[])++loopTails first++loopTails second
  | .dec _ _ _ inner | .decCall _ _ _ _ inner | .while _ inner=>loopTails inner
  | .ite _ first second=>loopTails first++loopTails second
  | _=>[]
def withdrawalSuffix : ProgHOL 64 := ((loopTails body)[1]?).getD .skip
def headerAssign (name : String) : ProgHOL 64 :=
  .call (some (some (.local,ofString "hl"),none)) (ofString "rlp_list_header_len") [localVar name]
def addWithdrawalExpression : ExpHOL 64 := .op .add [localVar "total",localVar "hl",localVar "wl"]
def lengthReturn : ProgHOL 64 := .return (.op .add [localVar "total",localVar "hl"])

theorem suffix_shape : withdrawalSuffix=.seq (headerAssign "wl")
    (.seq (.assign .local (ofString "total") addWithdrawalExpression) (.seq (headerAssign "total") lengthReturn)) := by
  simp only [withdrawalSuffix,loopTails,body,Guest.guestFn_block_rlp_length,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,
    List.nil_append,List.cons_append,List.append_nil,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    headerAssign,addWithdrawalExpression,lengthReturn,localVar]

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.suffix_shape
