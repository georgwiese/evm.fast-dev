import InitECandidate.Solver.Input.CurrentTable.NodeBuild.Iteration
import InitECandidate.Solver.Input.CounterFlow

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original unsigned loop condition compares the actual reached
counter/count words, including an empty database. -/
theorem test_read (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : State data origin source index) (layout : Layout data) (bounded : index≤data.total+1) :
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) condition=
      some (.val (.word (if index<data.total then 1#64 else 0#64))) := by
  simp [condition,evalHOLFinite,evalHOLExact,localVar,toExact,state.indexCell,state.countCell,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  all_goals simp only [Nat.mod_eq_of_lt (show index<18446744073709551616 from by have := layout.totalSmall; omega),
    Nat.mod_eq_of_lt (show data.total<18446744073709551616 from by have := layout.totalSmall; omega)]

theorem active_of_test (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : State data origin source index) (layout : Layout data) (bounded : index≤data.total+1) (word : BitVec 64)
    (read : evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) condition=some (.val (.word word)))
    (nonzero : word≠0#64) : index<data.total := by
  have actual:=test_read data origin source index state layout bounded
  apply Classical.byContradiction
  intro inactive
  rw [if_neg inactive] at actual
  have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans actual
  exact nonzero zero

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.test_read
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.active_of_test
