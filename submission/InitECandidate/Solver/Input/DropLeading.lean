import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang

def dropLeading : Nat→ProgHOL 64→ProgHOL 64
  | 0,code=>code
  | n+1,.seq _ rest=>dropLeading n rest
  | n+1,.dec _ _ _ rest=>dropLeading n rest
  | n+1,.decCall _ _ _ _ rest=>dropLeading n rest
  | _,_=>.skip
end InitECandidate.Solver.Input.Payload
