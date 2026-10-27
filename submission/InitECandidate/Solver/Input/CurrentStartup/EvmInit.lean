import InitECandidate.Solver.Input.CurrentStartup.Base
import InitECandidate.Solver.Input.CurrentStartup.Alloc
import InitECandidate.Solver.Input.CurrentStartup.HeapMark
import InitECandidate.Solver.Input.CurrentStartup.HeapRelease
import InitECandidate.Solver.Input.CurrentStartup.Keccak256
import InitECandidate.Solver.Input.CurrentStartup.Memzero

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace EvmInit
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .evm_init) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_evm_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .heap_mark) _ _ (Code.formals .heap_mark) (Code.body .heap_mark) (Code.shape .heap_mark)
  (Code.installed code installed .heap_mark) (HeapMark.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (Alloc.preserves cursor code installed)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .heap_release) _ (Code.formals .heap_release) (Code.body .heap_release) (Code.shape .heap_release)
  (Code.installed code installed .heap_release) (HeapRelease.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_call_body (key cursor) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases cursor <;> decide) (Code.installed code installed .alloc) (Alloc.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .keccak256) _ (Code.formals .keccak256) (Code.body .keccak256) (Code.shape .keccak256)
  (Code.installed code installed .keccak256) (Keccak256.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_call_body (key cursor) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases cursor <;> decide) (Code.installed code installed .alloc) (Alloc.preserves cursor code installed))
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.loop (key cursor) code _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.assign (key cursor) code _ _)))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_call_body (key cursor) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases cursor <;> decide) (Code.installed code installed .alloc) (Alloc.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (Memzero.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_call_body (key cursor) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases cursor <;> decide) (Code.installed code installed .alloc) (Alloc.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (Memzero.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_call_body (key cursor) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases cursor <;> decide) (Code.installed code installed .alloc) (Alloc.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_call_body (key cursor) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases cursor <;> decide) (Code.installed code installed .alloc) (Alloc.preserves cursor code installed))
  (GlobalEffects.returned (key cursor) code _)))))))))))))))))))))))))))))))))))))))))))))))))

end EvmInit
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.EvmInit.preserves
