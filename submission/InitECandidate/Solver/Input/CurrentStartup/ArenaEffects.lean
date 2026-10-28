import InitECandidate.Solver.Input.CurrentStartup.ArenaFrame
import InitECandidate.Solver.Input.GlobalEffects
import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual code/domain invariants and the two selected global frames retain
main's initialized arena even when a helper allocates persistent memory. -/
theorem ArenaState.after_globals {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    (arena : ArenaState source) (program : ProgHOL 64) (outcome : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source program=(outcome,post))
    (scratch : GlobalEffects.Preserves (ofString "scratch_ptr") source.code program)
    (frame : GlobalEffects.Preserves (ofString "frame_mem_ptr") source.code program) : ArenaState post := by
  have scratchFrame:=scratch source rfl
  have frameFrame:=frame source rfl
  rw [actual] at scratchFrame frameFrame
  have fields:=evaluation_fields source post program outcome actual
  exact ⟨(congrArg Prod.snd scratchFrame).trans arena.scratch,(congrArg Prod.snd frameFrame).trans arena.frame,
    fields.1.trans arena.domain,by rw [fields.2.2.2]; exact arena.code⟩

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.ArenaState.after_globals
