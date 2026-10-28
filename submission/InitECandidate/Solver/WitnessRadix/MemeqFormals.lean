import InitECandidate.Solver.WitnessRadix.Memeq32

namespace InitECandidate.Solver.WitnessRadix.Memeq32
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

def formals : List (MlS × ShapeHOL) :=
  [(ofString "a", .one), (ofString "b", .one), (ofString "n", .one)]

end InitECandidate.Solver.WitnessRadix.Memeq32
