import InitECandidate.Solver.Input.CallPrefix
import Guest.Ast

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_payload_header with | .function fn=>progToHOL fn.body | _=>.skip
def parts := CallPrefix.cut (ofString "block_rlp_length") body
def actions := parts.1
def lengthCall := parts.2
def afterLength : ProgHOL 64 := match lengthCall with | .decCall _ _ _ _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem length_call_shape : lengthCall=.decCall (ofString "bl") .one (ofString "block_rlp_length") [localVar "h",localVar "pl"] afterLength := by
  simp only [lengthCall,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterLength,localVar]

theorem body_shape : body=CallPrefix.program actions lengthCall := (CallPrefix.reconstruct _ body).symm

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.length_call_shape
#print axioms InitECandidate.Solver.Input.PayloadHeader.body_shape
