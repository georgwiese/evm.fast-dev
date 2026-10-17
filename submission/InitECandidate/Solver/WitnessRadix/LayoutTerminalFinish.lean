import InitECandidate.Solver.WitnessRadix.LayoutTerminalBody
import InitECandidate.Solver.WitnessRadix.TerminalLoopFinish

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

theorem terminal_body_finish {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated 0 destination) (valid : Valid layout) (mapped : Mapped source layout)
    (branchRoom : allocated < layout.count) (locals : SplitCount.TaskLocals source context)
    (rows : BuildCopy.Rows source.memory source.memaddrs context.src (BitVec.ofNat 64 context.start) 0 context.input)
    (stop : context.input.length = 1 ∨ context.position = 256) (ordinal : BitVec 64) (last : context.input.getLast? = some ordinal) :
    ∃ target : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState source BuildEntry.mainBody = (some (.returned (.val (.word 0#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite (OpenGraph.leafPost source context.dest ordinal.toNat) := by
  obtain ⟨pool, offset, write, destEq⟩ := destination_writable layout context allocated 0 destination atLayout branchRoom
  have destinationMapped : source.memaddrs context.dest := by
    rw [destEq]
    have bound := write_word_bound layout valid pool offset write
    exact mapped pool offset bound.2 bound.1
  have depthLocal := locals.depthLocal
  rw [atLayout.depthEq] at depthLocal
  obtain ⟨target, run, fields⟩ := TerminalProgram.main_body_finish source context.dest ordinal
    (terminal_test_read source context locals stop)
    (BuildCopy.terminal_read source context.src context.start context.input ordinal locals.srcLocal locals.startLocal locals.countLocal rows last)
    locals.destLocal depthLocal destinationMapped
  exact ⟨target, run, by simpa only [OpenGraph.leafPost, tag_word] using fields⟩

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.terminal_body_finish
