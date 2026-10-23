import InitECandidate.Solver.Mpt.NibblesConcatProgram
import InitECandidate.Solver.Input.BufferGlobals
import InitECandidate.Solver.WitnessRadix.AllocationGlobals

namespace InitECandidate.Solver.Mpt.NibblesConcat
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The original concatenation updates only the heap global, including
on failed allocations or copies. In particular it retains both low cursors. -/
theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    Input.GlobalEffects.Preserves key code body := by
  rw [body_shapes.1]
  apply Input.GlobalEffects.scoped_body key code (ofString "out") .one (ofString "alloc") _ _ PersistentAlloc.formals PersistentAlloc.body .one
    (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed other)
  rw [body_shapes.2.1,body_shapes.2.2.1,body_shapes.2.2.2]
  unfold firstCopy secondCopy
  repeat first
    | apply Input.GlobalEffects.sequence
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "memcpy") _ CopyGeneral.formals Copy32.body .one
        (GasBudget.Mcopy.copy_code code installed) (Copy32.globals key code)

end InitECandidate.Solver.Mpt.NibblesConcat

#print axioms InitECandidate.Solver.Mpt.NibblesConcat.globals
