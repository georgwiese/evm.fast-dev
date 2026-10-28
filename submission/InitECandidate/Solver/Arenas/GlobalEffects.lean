import InitECandidate.Solver.Input.GlobalEffectsAtoms
import InitECandidate.Solver.Input.GlobalEffectsScoped
import InitECandidate.Solver.Arenas.ScratchScope

namespace InitECandidate.Solver.Input.Trap
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem globals (key : MlS) (code) : GlobalEffects.Preserves key code body := by
  simp only [body,Guest.Software.guestFn_trap_with,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | apply GlobalEffects.sequence
    | exact GlobalEffects.shared_store key code _ _ _
    | exact GlobalEffects.external key code _ _ _ _ _
    | exact GlobalEffects.raised key code _ _

end InitECandidate.Solver.Input.Trap

namespace InitECandidate.Solver.Arenas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (direction : Direction)
    (other : key≠ofString (pointerName direction)) : Input.GlobalEffects.Preserves key code (body direction) := by
  rw [body_shape]
  simp only [program,pTail,qTail,firstGuard,secondGuard,trap,assignment]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | exact Input.GlobalEffects.global_other key code _ _ other
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.skip key code
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "trap_with") _ Input.Trap.formals Input.Trap.body .one
        (Input.Trap.original_code code installed) (Input.Trap.globals key code)

theorem mark_globals (key : MlS) (code) (direction : Direction) : Input.GlobalEffects.Preserves key code (markBody direction) := by
  rw [mark_body]
  exact Input.GlobalEffects.returned key code _

theorem Scratch.release_globals (key : MlS) (code) (other : key≠ofString "scratch_ptr") :
    Input.GlobalEffects.Preserves key code Scratch.releaseBody := by
  rw [Scratch.release_shape]
  exact Input.GlobalEffects.sequence key code _ _ (Input.GlobalEffects.global_other key code _ _ other) (Input.GlobalEffects.returned key code _)

end InitECandidate.Solver.Arenas

#print axioms InitECandidate.Solver.Input.Trap.globals
#print axioms InitECandidate.Solver.Arenas.globals
#print axioms InitECandidate.Solver.Arenas.mark_globals
#print axioms InitECandidate.Solver.Arenas.Scratch.release_globals
