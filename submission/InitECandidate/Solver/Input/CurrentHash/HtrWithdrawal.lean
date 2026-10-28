import InitECandidate.Solver.Input.CurrentHash.Base
import InitECandidate.Solver.Input.CurrentHash.SharedEffects
import InitECandidate.Solver.Input.CurrentHash.HtrBytesVector
import InitECandidate.Solver.Input.CurrentHash.HtrU64At
import InitECandidate.Solver.Input.CurrentHash.Merkleize

namespace InitECandidate.Solver.Input.CurrentHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace HtrWithdrawal
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .htr_withdrawal) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_htr_withdrawal, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .heap_mark) _ _ (Code.formals .heap_mark) (Code.body .heap_mark) (Code.shape .heap_mark)
  (Code.installed code installed .heap_mark) (SharedEffects.HeapMark.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (SharedEffects.Alloc.preserves cursor code installed)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_u64_at) _ (Code.formals .htr_u64_at) (Code.body .htr_u64_at) (Code.shape .htr_u64_at)
  (Code.installed code installed .htr_u64_at) (HtrU64At.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_u64_at) _ (Code.formals .htr_u64_at) (Code.body .htr_u64_at) (Code.shape .htr_u64_at)
  (Code.installed code installed .htr_u64_at) (HtrU64At.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_bytes_vector) _ (Code.formals .htr_bytes_vector) (Code.body .htr_bytes_vector) (Code.shape .htr_bytes_vector)
  (Code.installed code installed .htr_bytes_vector) (HtrBytesVector.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_u64_at) _ (Code.formals .htr_u64_at) (Code.body .htr_u64_at) (Code.shape .htr_u64_at)
  (Code.installed code installed .htr_u64_at) (HtrU64At.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .merkleize) _ (Code.formals .merkleize) (Code.body .merkleize) (Code.shape .merkleize)
  (Code.installed code installed .merkleize) (Merkleize.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .heap_release) _ (Code.formals .heap_release) (Code.body .heap_release) (Code.shape .heap_release)
  (Code.installed code installed .heap_release) (SharedEffects.HeapRelease.preserves cursor code installed))
  (GlobalEffects.returned (key cursor) code _)))))))))

end HtrWithdrawal
end InitECandidate.Solver.Input.CurrentHash

#print axioms InitECandidate.Solver.Input.CurrentHash.HtrWithdrawal.preserves
