import InitECandidate.Solver.Input.CurrentStartup.Base
import InitECandidate.Solver.Input.CurrentStartup.AddrFromWords
import InitECandidate.Solver.Input.CurrentStartup.Alloc
import InitECandidate.Solver.Input.CurrentStartup.Memzero
import InitECandidate.Solver.Input.CurrentStartup.StBe64

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace ForkInit
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .fork_init) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_fork_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_call_body (key cursor) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases cursor <;> decide) (Code.installed code installed .alloc) (Alloc.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (Memzero.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_call_body (key cursor) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases cursor <;> decide) (Code.installed code installed .alloc) (Alloc.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (Memzero.preserves cursor code installed))
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.loop (key cursor) code _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.assign (key cursor) code _ _)))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.byte_store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_call_body (key cursor) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases cursor <;> decide) (Code.installed code installed .alloc) (Alloc.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (AddrFromWords.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_call_body (key cursor) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases cursor <;> decide) (Code.installed code installed .alloc) (Alloc.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (AddrFromWords.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_call_body (key cursor) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases cursor <;> decide) (Code.installed code installed .alloc) (Alloc.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (AddrFromWords.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_call_body (key cursor) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases cursor <;> decide) (Code.installed code installed .alloc) (Alloc.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (AddrFromWords.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_call_body (key cursor) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases cursor <;> decide) (Code.installed code installed .alloc) (Alloc.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (AddrFromWords.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_call_body (key cursor) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases cursor <;> decide) (Code.installed code installed .alloc) (Alloc.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (AddrFromWords.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_call_body (key cursor) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases cursor <;> decide) (Code.installed code installed .alloc) (Alloc.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (AddrFromWords.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.global_call_body (key cursor) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases cursor <;> decide) (Code.installed code installed .alloc) (Alloc.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (StBe64.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (StBe64.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (StBe64.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (StBe64.preserves cursor code installed))
  (GlobalEffects.returned (key cursor) code _)))))))))))))))))))))))))))

end ForkInit
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.ForkInit.preserves
