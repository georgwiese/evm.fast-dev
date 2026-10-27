import InitECandidate.Solver.Input.CurrentHash.Base
import InitECandidate.Solver.Input.CurrentStartup.Alloc
import InitECandidate.Solver.Input.CurrentStartup.HeapMark
import InitECandidate.Solver.Input.CurrentStartup.HeapRelease
import InitECandidate.Solver.Input.CurrentHash.HtrBytesList
import InitECandidate.Solver.Input.CurrentHash.HtrBytesVector
import InitECandidate.Solver.Input.CurrentHash.HtrPbytes
import InitECandidate.Solver.Input.CurrentHash.HtrPcontainer
import InitECandidate.Solver.Input.CurrentHash.HtrPlistChunks
import InitECandidate.Solver.Input.CurrentHash.HtrU64At
import InitECandidate.Solver.Input.CurrentHash.HtrWithdrawal
import InitECandidate.Solver.Input.CurrentStartup.Memcpy

namespace InitECandidate.Solver.Input.CurrentHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace HtrPayload
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .htr_payload) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_htr_payload, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .heap_mark) _ _ (Code.formals .heap_mark) (Code.body .heap_mark) (Code.shape .heap_mark)
  (Code.installed code installed .heap_mark) (CurrentStartup.HeapMark.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (CurrentStartup.Alloc.preserves cursor code installed)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .memcpy) _ (Code.formals .memcpy) (Code.body .memcpy) (Code.shape .memcpy)
  (Code.installed code installed .memcpy) (CurrentStartup.Memcpy.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_bytes_vector) _ (Code.formals .htr_bytes_vector) (Code.body .htr_bytes_vector) (Code.shape .htr_bytes_vector)
  (Code.installed code installed .htr_bytes_vector) (HtrBytesVector.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .memcpy) _ (Code.formals .memcpy) (Code.body .memcpy) (Code.shape .memcpy)
  (Code.installed code installed .memcpy) (CurrentStartup.Memcpy.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .memcpy) _ (Code.formals .memcpy) (Code.body .memcpy) (Code.shape .memcpy)
  (Code.installed code installed .memcpy) (CurrentStartup.Memcpy.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_bytes_vector) _ (Code.formals .htr_bytes_vector) (Code.body .htr_bytes_vector) (Code.shape .htr_bytes_vector)
  (Code.installed code installed .htr_bytes_vector) (HtrBytesVector.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .memcpy) _ (Code.formals .memcpy) (Code.body .memcpy) (Code.shape .memcpy)
  (Code.installed code installed .memcpy) (CurrentStartup.Memcpy.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_u64_at) _ (Code.formals .htr_u64_at) (Code.body .htr_u64_at) (Code.shape .htr_u64_at)
  (Code.installed code installed .htr_u64_at) (HtrU64At.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_u64_at) _ (Code.formals .htr_u64_at) (Code.body .htr_u64_at) (Code.shape .htr_u64_at)
  (Code.installed code installed .htr_u64_at) (HtrU64At.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_u64_at) _ (Code.formals .htr_u64_at) (Code.body .htr_u64_at) (Code.shape .htr_u64_at)
  (Code.installed code installed .htr_u64_at) (HtrU64At.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_u64_at) _ (Code.formals .htr_u64_at) (Code.body .htr_u64_at) (Code.shape .htr_u64_at)
  (Code.installed code installed .htr_u64_at) (HtrU64At.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_bytes_list) _ (Code.formals .htr_bytes_list) (Code.body .htr_bytes_list) (Code.shape .htr_bytes_list)
  (Code.installed code installed .htr_bytes_list) (HtrBytesList.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .memcpy) _ (Code.formals .memcpy) (Code.body .memcpy) (Code.shape .memcpy)
  (Code.installed code installed .memcpy) (CurrentStartup.Memcpy.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .memcpy) _ (Code.formals .memcpy) (Code.body .memcpy) (Code.shape .memcpy)
  (Code.installed code installed .memcpy) (CurrentStartup.Memcpy.preserves cursor code installed))
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .heap_mark) _ _ (Code.formals .heap_mark) (Code.body .heap_mark) (Code.shape .heap_mark)
  (Code.installed code installed .heap_mark) (CurrentStartup.HeapMark.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (CurrentStartup.Alloc.preserves cursor code installed)
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.loop (key cursor) code _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_pbytes) _ (Code.formals .htr_pbytes) (Code.body .htr_pbytes) (Code.shape .htr_pbytes)
  (Code.installed code installed .htr_pbytes) (HtrPbytes.preserves cursor code installed))
  (GlobalEffects.assign (key cursor) code _ _)))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_plist_chunks) _ (Code.formals .htr_plist_chunks) (Code.body .htr_plist_chunks) (Code.shape .htr_plist_chunks)
  (Code.installed code installed .htr_plist_chunks) (HtrPlistChunks.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .heap_release) _ (Code.formals .heap_release) (Code.body .heap_release) (Code.shape .heap_release)
  (Code.installed code installed .heap_release) (CurrentStartup.HeapRelease.preserves cursor code installed))
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some (some _)) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (CurrentStartup.Alloc.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.assign (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.loop (key cursor) code _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_withdrawal) _ (Code.formals .htr_withdrawal) (Code.body .htr_withdrawal) (Code.shape .htr_withdrawal)
  (Code.installed code installed .htr_withdrawal) (HtrWithdrawal.preserves cursor code installed))
  (GlobalEffects.assign (key cursor) code _ _)))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_plist_chunks) _ (Code.formals .htr_plist_chunks) (Code.body .htr_plist_chunks) (Code.shape .htr_plist_chunks)
  (Code.installed code installed .htr_plist_chunks) (HtrPlistChunks.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .heap_release) _ (Code.formals .heap_release) (Code.body .heap_release) (Code.shape .heap_release)
  (Code.installed code installed .heap_release) (CurrentStartup.HeapRelease.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_u64_at) _ (Code.formals .htr_u64_at) (Code.body .htr_u64_at) (Code.shape .htr_u64_at)
  (Code.installed code installed .htr_u64_at) (HtrU64At.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_u64_at) _ (Code.formals .htr_u64_at) (Code.body .htr_u64_at) (Code.shape .htr_u64_at)
  (Code.installed code installed .htr_u64_at) (HtrU64At.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_pbytes) _ (Code.formals .htr_pbytes) (Code.body .htr_pbytes) (Code.shape .htr_pbytes)
  (Code.installed code installed .htr_pbytes) (HtrPbytes.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_u64_at) _ (Code.formals .htr_u64_at) (Code.body .htr_u64_at) (Code.shape .htr_u64_at)
  (Code.installed code installed .htr_u64_at) (HtrU64At.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_pcontainer) _ (Code.formals .htr_pcontainer) (Code.body .htr_pcontainer) (Code.shape .htr_pcontainer)
  (Code.installed code installed .htr_pcontainer) (HtrPcontainer.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .heap_release) _ (Code.formals .heap_release) (Code.body .heap_release) (Code.shape .heap_release)
  (Code.installed code installed .heap_release) (CurrentStartup.HeapRelease.preserves cursor code installed))
  (GlobalEffects.returned (key cursor) code _))))))))))))))))))))))))))))))))))))))

end HtrPayload
end InitECandidate.Solver.Input.CurrentHash

#print axioms InitECandidate.Solver.Input.CurrentHash.HtrPayload.preserves
