import InitECandidate.Solver.Input.ScalarDeclaration

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A mapped scalar word load, independent of any witness-decoder pipeline. -/
theorem load_word_read {F : Type} (source : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64)
    (address value : BitVec 64) (read : eval source expression=some (.val (.word address)))
    (mapped : source.memaddrs address) (cell : source.memory address=.word value) :
    eval source (.load .one expression)=some (.val (.word value)) := by
  classical
  simp only [eval] at read ⊢
  simp [evalHOLExact,read,memLoadHOLExact,isWfShapeExactHOL,toExact,mapped,cell]


end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.load_word_read
