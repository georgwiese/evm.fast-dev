import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang

def values (pointer length limit maximum : BitVec 64) : List (ValueHOL 64) :=
  [.val (.word pointer), .val (.word length), .val (.word limit), .val (.word maximum)]

end InitECandidate.Solver.Input.BytesList
