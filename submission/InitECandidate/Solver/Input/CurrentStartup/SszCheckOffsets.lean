import InitECandidate.Solver.Input.CurrentStartup.Base
import InitECandidate.Solver.Input.CurrentStartup.SszFail

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace SszCheckOffsets
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .ssz_check_offsets) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_ssz_check_offsets, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.returned (key cursor) code _)
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.loop (key cursor) code _ _
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (SszFail.preserves cursor code installed))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (SszFail.preserves cursor code installed))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.assign (key cursor) code _ _)))))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (SszFail.preserves cursor code installed))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.returned (key cursor) code _)))))

end SszCheckOffsets
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.SszCheckOffsets.preserves
