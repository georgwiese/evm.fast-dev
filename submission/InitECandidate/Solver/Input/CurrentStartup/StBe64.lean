import InitECandidate.Solver.Input.CurrentStartup.Base
import InitECandidate.Solver.Input.CurrentStartup.Bswap64
import InitECandidate.Solver.Input.CurrentStartup.StBe32

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace StBe64
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .st_be64) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_st_be64, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .bswap64) _ _ (Code.formals .bswap64) (Code.body .bswap64) (Code.shape .bswap64)
  (Code.installed code installed .bswap64) (Bswap64.preserves cursor code installed)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.returned (key cursor) code _)))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .st_be32) _ (Code.formals .st_be32) (Code.body .st_be32) (Code.shape .st_be32)
  (Code.installed code installed .st_be32) (StBe32.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .st_be32) _ (Code.formals .st_be32) (Code.body .st_be32) (Code.shape .st_be32)
  (Code.installed code installed .st_be32) (StBe32.preserves cursor code installed))
  (GlobalEffects.returned (key cursor) code _))))

end StBe64
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.StBe64.preserves
