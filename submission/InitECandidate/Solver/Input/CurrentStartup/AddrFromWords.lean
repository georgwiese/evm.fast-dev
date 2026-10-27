import InitECandidate.Solver.Input.CurrentStartup.Base
import InitECandidate.Solver.Input.CurrentStartup.StBe32
import InitECandidate.Solver.Input.CurrentStartup.StBe64

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace AddrFromWords
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .addr_from_words) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_addr_from_words, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .st_be32) _ (Code.formals .st_be32) (Code.body .st_be32) (Code.shape .st_be32)
  (Code.installed code installed .st_be32) (StBe32.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (StBe64.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (StBe64.preserves cursor code installed))
  (GlobalEffects.returned (key cursor) code _))))

end AddrFromWords
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.AddrFromWords.preserves
