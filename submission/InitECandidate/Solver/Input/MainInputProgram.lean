import InitECandidate.Solver.Input.MainInputEntry
import InitECandidate.Solver.Input.BlobCallEnvironment

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def afterInput : ProgHOL 64 := match afterFork with | .decCall _ _ _ _ rest => rest | _ => .skip

set_option maxRecDepth 100000 in
theorem after_fork_shape : afterFork = .decCall (ofString "inp") Blob.returnShape (ofString "input_blob") [] afterInput := by
  simp only [afterFork,afterEvm,afterHeader,afterBlake,afterRipemd,afterBls,afterBn,afterSecp,afterU256,afterMpt,afterSsz,afterKeccak,afterSha,afterMemory,body,
    afterInput,Blob.returnShape,Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.after_fork_shape
