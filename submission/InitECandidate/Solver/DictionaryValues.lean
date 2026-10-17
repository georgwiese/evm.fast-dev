import InitECandidate.Solver.PanState
import InitECandidate.Solver.WitnessRadix.Graph

namespace InitECandidate.Solver.WitnessRadix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def QueryEmpty.zeros : ValueHOL 64 := .rStruct [.val (.word 0), .val (.word 0), .val (.word 0)]
def QueryLeaf.found (pointer length : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word 1#64), .val (.word pointer), .val (.word length)]
def QueryExecution.valueOf : Option Graph.Slice → ValueHOL 64
  | none => QueryEmpty.zeros
  | some value => QueryLeaf.found value.1 value.2

end InitECandidate.Solver.WitnessRadix
