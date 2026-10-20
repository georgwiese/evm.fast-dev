import InitECandidate.Solver.Input.MainDecoderCall

namespace InitECandidate.Solver.Input.Main.ErrorHandler
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def arguments : List (ExpHOL 64) := [localVar "out",localVar "z32",.const 0#64,.const 0#64,.const 0#64]
def resultLength : ExpHOL 64 := .op .add [localVar "n",.const 1#64]
def append : ProgHOL 64 := .storeByte (.op .add [localVar "out",localVar "n"]) (localVar "err_code")
def outputArgs : List (ExpHOL 64) := [localVar "out",resultLength]
def halt : ProgHOL 64 := .extCall (ofString "halt") .baseAddr (.const 0#64) .baseAddr (.const 0#64)
def suffix : ProgHOL 64 := .seq halt (.return (.const 1#64))
def tail : ProgHOL 64 := .seq append (.seq (.call (some (none,none)) (ofString "output_write") outputArgs) suffix)

set_option maxRecDepth 100000 in
theorem original_shape : DecoderCall.handler = .decCall (ofString "n") .one (ofString "serialize_result") arguments tail := by
  simp only [DecoderCall.handler,DecoderCall.program,DecoderSetup.decoder,DecoderSetup.afterZeroAllocation,DecoderSetup.afterOutAllocation,
    afterInput,afterFork,afterEvm,afterHeader,afterBlake,afterRipemd,afterBls,afterBn,afterSecp,afterU256,afterMpt,afterSsz,afterKeccak,afterSha,afterMemory,Main.body,
    Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    arguments,tail,append,outputArgs,suffix,halt,resultLength,localVar]

end InitECandidate.Solver.Input.Main.ErrorHandler

#print axioms InitECandidate.Solver.Input.Main.ErrorHandler.original_shape
