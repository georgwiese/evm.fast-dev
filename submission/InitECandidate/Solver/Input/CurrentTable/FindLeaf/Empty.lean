import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Entry

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual empty current traversal exits before reading any node or
key byte and spends no source loop clock, even with clock0. -/
theorem empty_loop (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (nodeCell : source.locals.lookup (ofString "n")=some (.val (.word 0#64))) :
    evaluateHOLFiniteState source loop=(none,source) := by
  have read:=test_read source 0#64 nodeCell
  rw [shapes.1,evaluateHOLFiniteState_while_total,read]
  simp

/-- A physical current empty table returns its literal zero root without
spending a body source clock. No initialized node-array contents, key-byte
mapping or future successful table operation is required. -/
theorem body_empty (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table base : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena table 88) (aligned : table.toNat%8=0)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.memory table=.word 32#64) (nodesCell : source.memory (table+40#64)=.word base)
    (rootCell : source.memory (table+56#64)=.word 0#64) :
    (evaluateHOLFiniteState source body).1=some (.returned (.val (.word 0#64))) ∧
    (evaluateHOLFiniteState source body).2.clock=source.clock ∧
    LocalEffects.erase (evaluateHOLFiniteState source body).2=LocalEffects.erase source := by
  have state:=root_state source base 0#64
  have loopRun:=empty_loop (rootEntry source base 0#64) state.nodeCell
  have afterRun : evaluateHOLFiniteState (rootEntry source base 0#64) afterRoot=
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (rootEntry source base 0#64)) := by
    rw [body_shapes.2.2.2,evaluateHOLFiniteState_seq_line780,loopRun]
    simp [evaluateHOLFiniteState_return,evalHOLExact,localVar,state.nodeCell,shapeOfHOLExact]
  rw [setup_execute source table base 0#64 domain arena aligned tableCell keyCell nodesCell rootCell,afterRun]
  exact ⟨rfl,rfl,rfl⟩

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.empty_loop
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.body_empty
