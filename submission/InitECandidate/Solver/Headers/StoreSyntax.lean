import InitECandidate.Solver.Headers.StoreValue

namespace InitECandidate.Solver.Headers
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

def storeAddress (offset : Nat) : ExpHOL 64 := .op .add [.var .local (ofString "h"),.const (BitVec.ofNat 64 offset)]
def storeProgram (offset : Nat) (value : StoreValue) : ProgHOL 64 := .store (storeAddress offset) value.expression

end InitECandidate.Solver.Headers
