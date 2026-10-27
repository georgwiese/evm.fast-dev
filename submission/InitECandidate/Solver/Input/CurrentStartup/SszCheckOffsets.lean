import InitECandidate.Solver.Input.CurrentStartup.Base
import InitECandidate.Solver.Input.CurrentStartup.SszFail

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace SszCheckOffsets
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem any_key (selected : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves selected code (Code.body .ssz_check_offsets) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_ssz_check_offsets, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence selected code _ _
  (GlobalEffects.conditional selected code _ _ _
  (GlobalEffects.returned selected code _)
  (GlobalEffects.skip selected code))
  (GlobalEffects.declared selected code _ _ _ _
  (GlobalEffects.sequence selected code _ _
  (GlobalEffects.loop selected code _ _
  (GlobalEffects.declared selected code _ _ _ _
  (GlobalEffects.sequence selected code _ _
  (GlobalEffects.conditional selected code _ _ _
  (GlobalEffects.call_body selected code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (SszFail.any_key selected code installed))
  (GlobalEffects.skip selected code))
  (GlobalEffects.sequence selected code _ _
  (GlobalEffects.conditional selected code _ _ _
  (GlobalEffects.conditional selected code _ _ _
  (GlobalEffects.call_body selected code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (SszFail.any_key selected code installed))
  (GlobalEffects.skip selected code))
  (GlobalEffects.skip selected code))
  (GlobalEffects.assign selected code _ _)))))
  (GlobalEffects.sequence selected code _ _
  (GlobalEffects.conditional selected code _ _ _
  (GlobalEffects.call_body selected code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (SszFail.any_key selected code installed))
  (GlobalEffects.skip selected code))
  (GlobalEffects.returned selected code _)))))

theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .ssz_check_offsets) :=
  any_key (key cursor) code installed

end SszCheckOffsets
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.SszCheckOffsets.preserves

#print axioms InitECandidate.Solver.Input.CurrentStartup.SszCheckOffsets.any_key
