import InitECandidate.Solver.Input.CurrentStartup.Base
import InitECandidate.Solver.Input.CurrentStartup.Alloc
import InitECandidate.Solver.Input.CurrentStartup.SszCheckOffsets
import InitECandidate.Solver.Input.CurrentStartup.SszFail
import InitECandidate.Solver.Input.CurrentStartup.SszFixedListCount

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace DecodeRequests
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .decode_requests) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_decode_requests, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (SszFail.preserves cursor code installed))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.loop (key cursor) code _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.assign (key cursor) code _ _)))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .ssz_check_offsets) _ (Code.formals .ssz_check_offsets) (Code.body .ssz_check_offsets) (Code.shape .ssz_check_offsets)
  (Code.installed code installed .ssz_check_offsets) (SszCheckOffsets.preserves cursor code installed))
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (Alloc.preserves cursor code installed)
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .ssz_fixed_list_count) _ _ (Code.formals .ssz_fixed_list_count) (Code.body .ssz_fixed_list_count) (Code.shape .ssz_fixed_list_count)
  (Code.installed code installed .ssz_fixed_list_count) (SszFixedListCount.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .ssz_fixed_list_count) _ _ (Code.formals .ssz_fixed_list_count) (Code.body .ssz_fixed_list_count) (Code.shape .ssz_fixed_list_count)
  (Code.installed code installed .ssz_fixed_list_count) (SszFixedListCount.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .ssz_fixed_list_count) _ _ (Code.formals .ssz_fixed_list_count) (Code.body .ssz_fixed_list_count) (Code.shape .ssz_fixed_list_count)
  (Code.installed code installed .ssz_fixed_list_count) (SszFixedListCount.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .ssz_fixed_list_count) _ _ (Code.formals .ssz_fixed_list_count) (Code.body .ssz_fixed_list_count) (Code.shape .ssz_fixed_list_count)
  (Code.installed code installed .ssz_fixed_list_count) (SszFixedListCount.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .ssz_fixed_list_count) _ _ (Code.formals .ssz_fixed_list_count) (Code.body .ssz_fixed_list_count) (Code.shape .ssz_fixed_list_count)
  (Code.installed code installed .ssz_fixed_list_count) (SszFixedListCount.preserves cursor code installed)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.returned (key cursor) code _))))))))))))))))))))))))))

end DecodeRequests
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.DecodeRequests.preserves
