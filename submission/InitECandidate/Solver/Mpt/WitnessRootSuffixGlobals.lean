import InitECandidate.Solver.Mpt.WitnessRootGlobals

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem cache_guard_globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code)
    (notHeap : key≠ofString "heap_ptr") : Input.GlobalEffects.Preserves key code cacheGuard:=by
  simp only [cacheGuard,cacheAllocated,rootCopy,rootCache]
  repeat first
    | apply Input.GlobalEffects.conditional
    | apply Input.GlobalEffects.sequence
    | exact Input.GlobalEffects.skip key code
    | exact Input.GlobalEffects.store key code _ _
    | apply Input.GlobalEffects.scoped_body key code (ofString "h") .one (ofString "alloc") _ _ PersistentAlloc.formals PersistentAlloc.body .one
        (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed notHeap)
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "memcpy") _ CopyGeneral.formals Copy32.body .one
        (CopyGeneral.original_code code installed) (CopyGeneral.globals key code)

/-- The genuine post-materializer cache/footer retains scratch and every
other nonheap global on all outcomes. -/
theorem suffix_globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code)
    (notHeap : key≠ofString "heap_ptr") : Input.GlobalEffects.Preserves key code afterMaterialize:=by
  rw [suffix_shape]
  exact Input.GlobalEffects.sequence key code _ _ (cache_guard_globals key code installed notHeap) (Input.GlobalEffects.returned key code _)

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.cache_guard_globals
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.suffix_globals
