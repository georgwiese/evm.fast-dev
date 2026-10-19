import InitECandidate.Solver.Mpt.KeyToNibblesProgram
import InitECandidate.Solver.Input.ByteStoreNoException
import InitECandidate.Solver.Input.NoExceptionLoop
import InitECandidate.Solver.Input.NoExceptionCall

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 10000 in
theorem no_exception (code) : Input.NoException.Safe code body := by
  simp only [body, Guest.guestFn_key_to_nibbles, progToHOL]
  repeat first
    | apply Input.NoException.declared
    | apply Input.NoException.sequence
    | apply Input.NoException.loop
    | exact Input.NoException.store_byte code _ _
    | exact Input.NoException.assign code _ _
    | exact Input.NoException.returned code _

theorem call_no_exception (code) (installed : Input.OriginalCode.Installed code) (arguments : List (ExpHOL 64)) :
    Input.NoException.Safe code (.call (some (none, none)) (ofString "key_to_nibbles") arguments) :=
  Input.NoException.call_body code (ofString "key_to_nibbles") arguments formals body .one (original_code code installed) (no_exception code)

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.no_exception
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.call_no_exception
