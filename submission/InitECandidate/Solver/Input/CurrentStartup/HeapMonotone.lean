import InitECandidate.Solver.Input.CurrentStartup.AllocationCursor
import InitECandidate.Solver.Input.NormalHeapCall
import InitECandidate.Solver.WitnessRadix.AllocationRequest

namespace InitECandidate.Solver.Input.CurrentStartup.HeapMonotone
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

-- Actual fixed-syntax proofs. The release operation is deliberately excluded;
-- its actual saved mark must be tracked in the EVM initializer separately.

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem trap_with (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .trap_with) := by
  intro source codeEq lower initial value returned
  have same : Code.body .trap_with = Trap.body := by
    simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL, funDeclToHOL, Guest.Software.guestFn_trap_with, Trap.body]
  rw [same] at returned
  exact (Trap.never_returns source value returned).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem alloc (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .alloc) := by
  intro source codeEq lower initial value returned
  obtain ⟨pointer, cell, lowerBound, bounded, aligned⟩ := initial
  have same : Code.body .alloc = WitnessRadix.PersistentAlloc.body := by
    simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL, funDeclToHOL, Guest.Software.guestFn_alloc, WitnessRadix.PersistentAlloc.body]
  rw [same] at returned
  have actual : evaluateHOLFiniteState source WitnessRadix.PersistentAlloc.body =
      (some (.returned value), (evaluateHOLFiniteState source WitnessRadix.PersistentAlloc.body).2) := Prod.ext returned rfl
  have codeInstalled : OriginalCode.Installed source.code := by rw [codeEq]; exact installed
  obtain ⟨next, heap, monotone, upper, multiple⟩ := WitnessRadix.PersistentAlloc.monotone_return source _ pointer cell bounded
    (trap_entry source.code codeInstalled) value actual
  exact ⟨next, heap, Nat.le_trans lowerBound monotone, upper, multiple⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem sha256_init (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .sha256_init) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_sha256_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.returned code _)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem keccak_init (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .keccak_init) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_keccak_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.returned code _))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ssz_init (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .ssz_init) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_ssz_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.conditional code _ _ _
  (NormalHeapEffects.returned code _)
  (NormalHeapEffects.skip code))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.returned code _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem keccak_f1600 (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .keccak_f1600) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_keccak_f1600, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.loop code _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.assign code _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.returned code _)))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem keccak_absorb_block (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .keccak_absorb_block) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_keccak_absorb_block, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.conditional code _ _ _
  (NormalHeapEffects.loop code _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.assign code _ _)))
  (NormalHeapEffects.loop code _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.assign code _ _))))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .keccak_f1600) _ (Code.formals .keccak_f1600) (Code.body .keccak_f1600) (Code.shape .keccak_f1600)
  (Code.installed code installed .keccak_f1600) (keccak_f1600 code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.returned code _))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem memcpy (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .memcpy) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_memcpy, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.conditional code _ _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.loop code _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.assign code _ _))))))
  (NormalHeapEffects.loop code _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.assign code _ _))))
  (NormalHeapEffects.skip code))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.loop code _ _
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
  (NormalHeapEffects.assign code _ _))))))))))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.loop code _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.assign code _ _)))
  (NormalHeapEffects.returned code _)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem memzero (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .memzero) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_memzero, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.conditional code _ _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.loop code _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.assign code _ _))))))
  (NormalHeapEffects.loop code _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.assign code _ _))))
  (NormalHeapEffects.skip code))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.loop code _ _
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
  (NormalHeapEffects.assign code _ _))))))))))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.loop code _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.assign code _ _)))
  (NormalHeapEffects.returned code _)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem keccak256 (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .keccak256) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_keccak256, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.loop code _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .keccak_absorb_block) _ (Code.formals .keccak_absorb_block) (Code.body .keccak_absorb_block) (Code.shape .keccak_absorb_block)
  (Code.installed code installed .keccak_absorb_block) (keccak_absorb_block code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.assign code _ _)))
  (NormalHeapEffects.declared code _ _ _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .memcpy) _ (Code.formals .memcpy) (Code.body .memcpy) (Code.shape .memcpy)
  (Code.installed code installed .memcpy) (memcpy code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .keccak_absorb_block) _ (Code.formals .keccak_absorb_block) (Code.body .keccak_absorb_block) (Code.shape .keccak_absorb_block)
  (Code.installed code installed .keccak_absorb_block) (keccak_absorb_block code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.conditional code _ _ _
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.store code _ _))))
  (NormalHeapEffects.call_body code (some none) (Code.name .memcpy) _ (Code.formals .memcpy) (Code.body .memcpy) (Code.shape .memcpy)
  (Code.installed code installed .memcpy) (memcpy code installed) (by unfold NormalHeapEffects.Safe; decide)))
  (NormalHeapEffects.returned code _))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem mpt_init (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .mpt_init) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_mpt_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .keccak256) _ (Code.formals .keccak256) (Code.body .keccak256) (Code.shape .keccak256)
  (Code.installed code installed .keccak256) (keccak256 code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .keccak256) _ (Code.formals .keccak256) (Code.body .keccak256) (Code.shape .keccak256)
  (Code.installed code installed .keccak256) (keccak256 code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.returned code _)))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem u256_ws_init (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .u256_ws_init) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_u256_ws_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.conditional code _ _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.skip code))
  (NormalHeapEffects.returned code _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem secp256k1_init (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .secp256k1_init) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_secp256k1_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.returned code _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bn254_init (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .bn254_init) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_bn254_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.conditional code _ _ _
  (NormalHeapEffects.returned code _)
  (NormalHeapEffects.skip code))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.returned code _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bls_consts_init (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .bls_consts_init) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_bls_consts_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.conditional code _ _ _
  (NormalHeapEffects.returned code _)
  (NormalHeapEffects.skip code))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.returned code _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bls_lib_init (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .bls_lib_init) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_bls_lib_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .bls_consts_init) _ (Code.formals .bls_consts_init) (Code.body .bls_consts_init) (Code.shape .bls_consts_init)
  (Code.installed code installed .bls_consts_init) (bls_consts_init code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.returned code _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bls_precompiles_init (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .bls_precompiles_init) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_bls_precompiles_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.conditional code _ _ _
  (NormalHeapEffects.returned code _)
  (NormalHeapEffects.skip code))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .bls_lib_init) _ (Code.formals .bls_lib_init) (Code.body .bls_lib_init) (Code.shape .bls_lib_init)
  (Code.installed code installed .bls_lib_init) (bls_lib_init code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.returned code _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ripemd160_init (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .ripemd160_init) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_ripemd160_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.conditional code _ _ _
  (NormalHeapEffects.returned code _)
  (NormalHeapEffects.skip code))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.returned code _))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem blake2_init (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .blake2_init) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_blake2_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.conditional code _ _ _
  (NormalHeapEffects.returned code _)
  (NormalHeapEffects.skip code))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.returned code _)))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem header_init (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .header_init) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_header_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.conditional code _ _ _
  (NormalHeapEffects.returned code _)
  (NormalHeapEffects.skip code))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.returned code _))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem st_be32 (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .st_be32) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_st_be32, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.byte_store code _ _)
  (NormalHeapEffects.returned code _)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bswap64 (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .bswap64) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_bswap64, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.assign code _ _)
  (NormalHeapEffects.returned code _)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem st_be64 (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .st_be64) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_st_be64, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.conditional code _ _ _
  (NormalHeapEffects.scoped_body code _ _ (Code.name .bswap64) _ _ (Code.formals .bswap64) (Code.body .bswap64) (Code.shape .bswap64)
  (Code.installed code installed .bswap64) (bswap64 code installed)
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.store code _ _)
  (NormalHeapEffects.returned code _)))
  (NormalHeapEffects.skip code))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .st_be32) _ (Code.formals .st_be32) (Code.body .st_be32) (Code.shape .st_be32)
  (Code.installed code installed .st_be32) (st_be32 code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .st_be32) _ (Code.formals .st_be32) (Code.body .st_be32) (Code.shape .st_be32)
  (Code.installed code installed .st_be32) (st_be32 code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.returned code _))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem addr_from_words (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .addr_from_words) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_addr_from_words, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .st_be32) _ (Code.formals .st_be32) (Code.body .st_be32) (Code.shape .st_be32)
  (Code.installed code installed .st_be32) (st_be32 code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.returned code _))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem fork_init (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .fork_init) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_fork_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed) (by unfold NormalHeapEffects.Safe; decide))
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
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.sequence code _ _
  (NormalHeapEffects.call_body code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed) (by unfold NormalHeapEffects.Safe; decide))
  (NormalHeapEffects.returned code _)))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem heap_mark (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .heap_mark) := by
  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_heap_mark, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHeapEffects.returned code _)

end InitECandidate.Solver.Input.CurrentStartup.HeapMonotone

#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.trap_with
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.alloc
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.sha256_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.keccak_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.ssz_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.keccak_f1600
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.keccak_absorb_block
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.memcpy
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.memzero
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.keccak256
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.mpt_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.u256_ws_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.secp256k1_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.bn254_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.bls_consts_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.bls_lib_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.bls_precompiles_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.ripemd160_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.blake2_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.header_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.st_be32
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.bswap64
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.st_be64
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.addr_from_words
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.fork_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.heap_mark
