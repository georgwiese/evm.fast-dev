import InitECandidate.Solver.Input.CurrentHash.Base
import InitECandidate.Solver.Input.CurrentStartup.Alloc
import InitECandidate.Solver.Input.CurrentStartup.HeapMark
import InitECandidate.Solver.Input.CurrentStartup.HeapRelease
import InitECandidate.Solver.Input.CurrentStartup.Memzero
import InitECandidate.Solver.Input.CurrentHash.MerkleizeProgressive
import InitECandidate.Solver.Input.CurrentHash.Sha256Pair

namespace InitECandidate.Solver.Input.CurrentHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace HtrPcontainer
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .htr_pcontainer) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_htr_pcontainer, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .heap_mark) _ _ (Code.formals .heap_mark) (Code.body .heap_mark) (Code.shape .heap_mark)
  (Code.installed code installed .heap_mark) (CurrentStartup.HeapMark.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (CurrentStartup.Alloc.preserves cursor code installed)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .merkleize_progressive) _ (Code.formals .merkleize_progressive) (Code.body .merkleize_progressive) (Code.shape .merkleize_progressive)
  (Code.installed code installed .merkleize_progressive) (MerkleizeProgressive.preserves cursor code installed))
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (CurrentStartup.Memzero.preserves cursor code installed))
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.loop (key cursor) code _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.assign (key cursor) code _ _)))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .sha256_pair) _ (Code.formals .sha256_pair) (Code.body .sha256_pair) (Code.shape .sha256_pair)
  (Code.installed code installed .sha256_pair) (Sha256Pair.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .heap_release) _ (Code.formals .heap_release) (Code.body .heap_release) (Code.shape .heap_release)
  (Code.installed code installed .heap_release) (CurrentStartup.HeapRelease.preserves cursor code installed))
  (GlobalEffects.returned (key cursor) code _))))))))))

end HtrPcontainer
end InitECandidate.Solver.Input.CurrentHash

#print axioms InitECandidate.Solver.Input.CurrentHash.HtrPcontainer.preserves
