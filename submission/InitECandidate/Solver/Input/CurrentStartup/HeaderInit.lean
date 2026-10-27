import InitECandidate.Solver.Input.CurrentStartup.Base
import InitECandidate.Solver.Input.CurrentStartup.Alloc
import InitECandidate.Solver.Input.CurrentStartup.Memzero

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace HeaderInit
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .header_init) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_header_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.returned (key cursor) code _)
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_call_body (key cursor) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases cursor <;> decide) (Code.installed code installed .alloc) (Alloc.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (Memzero.preserves cursor code installed))
  (GlobalEffects.returned (key cursor) code _))))

end HeaderInit
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.HeaderInit.preserves
