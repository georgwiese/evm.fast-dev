import InitECandidate.Solver.Input.PayloadHeaderProgram
import InitECandidate.Solver.Input.NoReturnAtoms

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
/-- No original initialization-prefix action can return payload_header's
value. A stopped prefix therefore cannot resume its outer hdr continuation. -/
theorem prefix_sink_never : NoReturn.Never (CallPrefix.program actions .skip) := by
  simp only [actions,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,CallPrefix.program]
  repeat' first
    | apply NoReturn.declared
    | apply NoReturn.scoped_call
    | apply NoReturn.sequence
    | exact NoReturn.ignored_call _ _
    | exact NoReturn.store _ _
    | exact NoReturn.store_byte _ _
    | exact NoReturn.skip

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.prefix_sink_never
