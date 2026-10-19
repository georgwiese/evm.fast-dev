import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch
attribute [local instance] Classical.propDecidable

/-- A known word cell either supplies its exact value or fails its actual
domain test. Mapping need not be assumed when pricing all outcomes. -/
theorem load_one_case {F : Type} (source : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64) (address value : BitVec 64)
    (addressRead : eval source expression=some (.val (.word address))) (cell : source.memory address=.word value) :
    eval source (.load .one expression)=if source.memaddrs address then some (.val (.word value)) else none := by
  classical
  simp only [eval] at addressRead ⊢
  rw [evalHOLExact,if_pos (by simp [isWfShapeExactHOL]),addressRead]
  simp [memLoadHOLExact,cell]

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.load_one_case
