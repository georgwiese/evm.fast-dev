import InitECandidate.Solver.Input.MainParsedInput

namespace InitECandidate.Solver.Input.Main.RequestHash
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
set_option maxRecDepth 100000

def afterRoot : ProgHOL 64 := match DecoderCall.continuation with | .decCall _ _ _ _ rest => rest | _ => .skip

def arguments : List (ExpHOL 64) := [localVar "si",localVar "root"]
def call : ProgHOL 64 := .call (some (none,none)) (ofString "htr_new_payload_request") arguments
def continuation : ProgHOL 64 := match afterRoot with | .seq _ rest => rest | _ => .skip

/-- Main's next literal32-byte allocation, original request-root call and
unchanged verification continuation; no alternative program is introduced. -/
theorem original_shape :
    DecoderCall.continuation=.decCall (ofString "root") .one (ofString "alloc") [.const 32#64] afterRoot ∧
      afterRoot=.seq call continuation := by
  simp only [DecoderCall.continuation,DecoderSetup.decoder,DecoderSetup.afterZeroAllocation,DecoderSetup.afterOutAllocation,
    afterInput,afterFork,afterEvm,afterHeader,afterBlake,afterRipemd,afterBls,afterBn,afterSecp,afterU256,afterMpt,afterSsz,afterKeccak,afterSha,afterMemory,Main.body,
    Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    afterRoot,call,arguments,continuation,localVar]
  trivial

end InitECandidate.Solver.Input.Main.RequestHash

#print axioms InitECandidate.Solver.Input.Main.RequestHash.original_shape
