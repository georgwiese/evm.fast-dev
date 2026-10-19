import InitECandidate.Solver.Arenas.GlobalEffects
import InitECandidate.Solver.WitnessRadix.AllocationCost

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    Input.GlobalEffects.Preserves key code body := by
  rw [body_shape]
  simp only [pTail,qTail,firstGuard,secondGuard,trap,assignment,returnPointer]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | exact Input.GlobalEffects.skip key code
    | exact Input.GlobalEffects.global_other key code _ _ other
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "trap_with") _ Input.Trap.formals Input.Trap.body .one
        (Input.Trap.original_code code installed) (Input.Trap.globals key code)

end InitECandidate.Solver.WitnessRadix.PersistentAlloc


#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.globals
