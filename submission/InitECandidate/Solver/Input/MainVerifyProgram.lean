import InitECandidate.Solver.Input.MainRootHashProgram
import InitECandidate.Solver.Input.VerifyProgram

namespace InitECandidate.Solver.Input.Main.Verification
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def arguments : List (ExpHOL 64) := [localVar "si"]
def afterVerify : ProgHOL 64 := match RequestHash.continuation with | .decCall _ _ _ _ rest=>rest | _=>.skip

set_option maxRecDepth 100000

/-- The actual unchanged main call, immediately after request-root hashing. -/
theorem original_shape : RequestHash.continuation=
    .decCall (ofString "succ") .one (ofString "verify_stateless_new_payload") arguments afterVerify := by
  simp only [RequestHash.continuation,RequestHash.afterRoot,DecoderCall.continuation,DecoderSetup.decoder,
    DecoderSetup.afterZeroAllocation,DecoderSetup.afterOutAllocation,afterInput,afterFork,afterEvm,afterHeader,
    afterBlake,afterRipemd,afterBls,afterBn,afterSecp,afterU256,afterMpt,afterSsz,afterKeccak,afterSha,afterMemory,
    Main.body,Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,
    Option.map_none,arguments,afterVerify,localVar]

end InitECandidate.Solver.Input.Main.Verification

#print axioms InitECandidate.Solver.Input.Main.Verification.original_shape
