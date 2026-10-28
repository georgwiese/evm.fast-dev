import InitECandidate.Solver.Input.CurrentHash.ProgressiveProgram
import InitECandidate.Solver.Input.WordTripleEnvironment

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

abbrev values := CallNormal.tripleValues

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (p n out : BitVec 64)
    (code : codeFn (ofString "merkleize_progressive")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "merkleize_progressive") (values p n out)=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word p)) ∧ callee.lookup (ofString "n")=some (.val (.word n)) ∧ callee.lookup (ofString "out")=some (.val (.word out)) :=
  CallNormal.triple_environment codeFn (ofString "merkleize_progressive") body p n out code

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.environment
