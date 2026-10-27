import InitECandidate.Solver.Input.CurrentStartup.Base
import InitECandidate.Solver.Input.CurrentStartup.TrapWith

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace Alloc
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .alloc) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_alloc, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .trap_with) _ (Code.formals .trap_with) (Code.body .trap_with) (Code.shape .trap_with)
  (Code.installed code installed .trap_with) (TrapWith.preserves cursor code installed))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .trap_with) _ (Code.formals .trap_with) (Code.body .trap_with) (Code.shape .trap_with)
  (Code.installed code installed .trap_with) (TrapWith.preserves cursor code installed))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_other (key cursor) code _ _ (by cases cursor <;> decide))
  (GlobalEffects.returned (key cursor) code _))))))

end Alloc
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.Alloc.preserves
