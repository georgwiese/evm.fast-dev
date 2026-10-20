import InitECandidate.Solver.Input.PackBytesProgram
import InitECandidate.Solver.WitnessRadix.AllocationGlobals

namespace InitECandidate.Solver.Input.PackBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Original byte packing only advances its actual heap cursor; every
initialized nonheap global survives every execution outcome. -/
theorem globals (key : MlS) (code) (installed : OriginalCode.Installed code) (other : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code body := by
  rw [body_shape.1,body_shape.2.1,body_shape.2.2.1,body_shape.2.2.2]
  apply GlobalEffects.declared
  apply GlobalEffects.scoped_body key code _ _ (ofString "alloc") _ _ _ _ _ (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed other)
  exact GlobalEffects.sequence key code _ _
    (GlobalEffects.call_body key code (some none) (ofString "memcpy") copyArguments CopyGeneral.formals Copy32.body .one (CopyGeneral.original_code code installed) (Copy32.globals key code))
    (GlobalEffects.sequence key code _ _ (GlobalEffects.call_body key code (some none) (ofString "memzero") zeroArguments Zero.formals Zero.body .one (Zero.original_code code installed) (Zero.globals key code))
      (GlobalEffects.returned key code _))

end InitECandidate.Solver.Input.PackBytes

#print axioms InitECandidate.Solver.Input.PackBytes.globals
