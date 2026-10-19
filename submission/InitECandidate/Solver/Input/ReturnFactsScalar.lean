import InitECandidate.Solver.Input.ReturnFacts
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Input.ReturnFacts
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem declared_word (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (expression : ExpHOL 64) (word : BitVec 64) (body : ProgHOL 64) (property : ValueHOL 64 → Prop)
    (read : eval source expression=some (.val (.word word)))
    (tail : Returns (bind source name word) body property) :
    Returns source (.dec (ofString name) .one expression body) property := by
  let entered := bind source name word
  have actual := ScalarScope.declare_execute source (evaluateHOLFiniteState entered body).2 name expression word body
    (evaluateHOLFiniteState entered body).1 read rfl
  intro target value normal
  have resultEq := congrArg Prod.fst (actual.symm.trans normal)
  exact tail (evaluateHOLFiniteState entered body).2 value (Prod.ext resultEq rfl)

theorem local_prefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key : MlS)
    (program : ProgHOL 64) (safe : LocalPrefix key program) (property : ValueHOL 64 → Prop) :
    Returns source program property := by
  intro target value normal
  have impossible := (safe.summary_full source).2.1 value
  exact (impossible (congrArg Prod.fst normal)).elim

end InitECandidate.Solver.Input.ReturnFacts

#print axioms InitECandidate.Solver.Input.ReturnFacts.declared_word
#print axioms InitECandidate.Solver.Input.ReturnFacts.local_prefix
