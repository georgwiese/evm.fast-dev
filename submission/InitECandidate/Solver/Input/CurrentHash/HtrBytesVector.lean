import InitECandidate.Solver.Input.CurrentHash.Base
import InitECandidate.Solver.Input.CurrentStartup.HeapMark
import InitECandidate.Solver.Input.CurrentStartup.HeapRelease
import InitECandidate.Solver.Input.CurrentStartup.Memcpy
import InitECandidate.Solver.Input.CurrentStartup.Memzero
import InitECandidate.Solver.Input.CurrentHash.Merkleize
import InitECandidate.Solver.Input.CurrentHash.PackBytes

namespace InitECandidate.Solver.Input.CurrentHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace HtrBytesVector
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .htr_bytes_vector) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_htr_bytes_vector, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (CurrentStartup.Memzero.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .memcpy) _ (Code.formals .memcpy) (Code.body .memcpy) (Code.shape .memcpy)
  (Code.installed code installed .memcpy) (CurrentStartup.Memcpy.preserves cursor code installed))
  (GlobalEffects.returned (key cursor) code _)))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .heap_mark) _ _ (Code.formals .heap_mark) (Code.body .heap_mark) (Code.shape .heap_mark)
  (Code.installed code installed .heap_mark) (CurrentStartup.HeapMark.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .pack_bytes) _ _ (Code.formals .pack_bytes) (Code.body .pack_bytes) (Code.shape .pack_bytes)
  (Code.installed code installed .pack_bytes) (PackBytes.preserves cursor code installed)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .merkleize) _ (Code.formals .merkleize) (Code.body .merkleize) (Code.shape .merkleize)
  (Code.installed code installed .merkleize) (Merkleize.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .heap_release) _ (Code.formals .heap_release) (Code.body .heap_release) (Code.shape .heap_release)
  (Code.installed code installed .heap_release) (CurrentStartup.HeapRelease.preserves cursor code installed))
  (GlobalEffects.returned (key cursor) code _))))))

end HtrBytesVector
end InitECandidate.Solver.Input.CurrentHash

#print axioms InitECandidate.Solver.Input.CurrentHash.HtrBytesVector.preserves
