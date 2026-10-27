import InitECandidate.Solver.Input.CurrentHash.Base
import InitECandidate.Solver.Input.CurrentHash.MerkleizeProgressive
import InitECandidate.Solver.Input.CurrentHash.MixInLength

namespace InitECandidate.Solver.Input.CurrentHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace HtrPlistChunks
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .htr_plist_chunks) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_htr_plist_chunks, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .merkleize_progressive) _ (Code.formals .merkleize_progressive) (Code.body .merkleize_progressive) (Code.shape .merkleize_progressive)
  (Code.installed code installed .merkleize_progressive) (MerkleizeProgressive.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .mix_in_length) _ (Code.formals .mix_in_length) (Code.body .mix_in_length) (Code.shape .mix_in_length)
  (Code.installed code installed .mix_in_length) (MixInLength.preserves cursor code installed))
  (GlobalEffects.returned (key cursor) code _)))

end HtrPlistChunks
end InitECandidate.Solver.Input.CurrentHash

#print axioms InitECandidate.Solver.Input.CurrentHash.HtrPlistChunks.preserves
