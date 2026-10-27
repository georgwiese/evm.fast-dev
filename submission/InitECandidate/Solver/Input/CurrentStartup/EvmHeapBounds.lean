import InitECandidate.Solver.Input.CurrentStartup.HeapMonotone
import InitECandidate.Solver.Input.CurrentStartup.EvmHeapProgram

namespace InitECandidate.Solver.Input.CurrentStartup.EvmHeap
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

-- Generated fixed-syntax contexts; the intervening release is handled using
-- its actual saved mark. Lean checks both contexts against literal source.

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem prefix_pure (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Preserves code (CallPrefix.program actions .skip) := by
  simp only [actions, CallPrefix.cutAt, CallPrefix.program, Code.body, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_evm_init, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.scoped_body code _ _ (Code.name .heap_mark) _ _ (Code.formals .heap_mark) (Code.body .heap_mark) (Code.shape .heap_mark)
  (Code.installed code installed .heap_mark) (HeapMonotone.heap_mark code installed)
  (NormalHeapEffects.scoped_body code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (HeapMonotone.alloc code installed)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.skip code))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem suffix_pure (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Preserves code (afterRelease) := by
  simp only [afterRelease, tail, CallPrefix.cutAt, Code.body, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_evm_init, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (HeapMonotone.alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .keccak256) _ (Code.formals .keccak256) (Code.body .keccak256) (Code.shape .keccak256)
  (Code.installed code installed .keccak256) (HeapMonotone.keccak256 code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (HeapMonotone.alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.loop code _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.assign code _ _)))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (HeapMonotone.alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (HeapMonotone.memzero code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (HeapMonotone.alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (HeapMonotone.memzero code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (HeapMonotone.alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (HeapMonotone.alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.returned code _)))))))))))))

end InitECandidate.Solver.Input.CurrentStartup.EvmHeap

#print axioms InitECandidate.Solver.Input.CurrentStartup.EvmHeap.prefix_pure
#print axioms InitECandidate.Solver.Input.CurrentStartup.EvmHeap.suffix_pure
