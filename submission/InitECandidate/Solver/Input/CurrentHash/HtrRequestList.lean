import InitECandidate.Solver.Input.CurrentHash.Base
import InitECandidate.Solver.Input.CurrentHash.SharedEffects
import InitECandidate.Solver.Input.CurrentHash.HtrBdep
import InitECandidate.Solver.Input.CurrentHash.HtrBexit
import InitECandidate.Solver.Input.CurrentHash.HtrCons
import InitECandidate.Solver.Input.CurrentHash.HtrDeposit
import InitECandidate.Solver.Input.CurrentHash.HtrPlistChunks
import InitECandidate.Solver.Input.CurrentHash.HtrWdreq

namespace InitECandidate.Solver.Input.CurrentHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace HtrRequestList
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .htr_request_list) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_htr_request_list, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .heap_mark) _ _ (Code.formals .heap_mark) (Code.body .heap_mark) (Code.shape .heap_mark)
  (Code.installed code installed .heap_mark) (SharedEffects.HeapMark.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (SharedEffects.Alloc.preserves cursor code installed)
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.loop (key cursor) code _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_deposit) _ (Code.formals .htr_deposit) (Code.body .htr_deposit) (Code.shape .htr_deposit)
  (Code.installed code installed .htr_deposit) (HtrDeposit.preserves cursor code installed))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_wdreq) _ (Code.formals .htr_wdreq) (Code.body .htr_wdreq) (Code.shape .htr_wdreq)
  (Code.installed code installed .htr_wdreq) (HtrWdreq.preserves cursor code installed))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_cons) _ (Code.formals .htr_cons) (Code.body .htr_cons) (Code.shape .htr_cons)
  (Code.installed code installed .htr_cons) (HtrCons.preserves cursor code installed))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_bdep) _ (Code.formals .htr_bdep) (Code.body .htr_bdep) (Code.shape .htr_bdep)
  (Code.installed code installed .htr_bdep) (HtrBdep.preserves cursor code installed))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_bexit) _ (Code.formals .htr_bexit) (Code.body .htr_bexit) (Code.shape .htr_bexit)
  (Code.installed code installed .htr_bexit) (HtrBexit.preserves cursor code installed))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.assign (key cursor) code _ _)))))))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .htr_plist_chunks) _ (Code.formals .htr_plist_chunks) (Code.body .htr_plist_chunks) (Code.shape .htr_plist_chunks)
  (Code.installed code installed .htr_plist_chunks) (HtrPlistChunks.preserves cursor code installed))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .heap_release) _ (Code.formals .heap_release) (Code.body .heap_release) (Code.shape .heap_release)
  (Code.installed code installed .heap_release) (SharedEffects.HeapRelease.preserves cursor code installed))
  (GlobalEffects.returned (key cursor) code _)))))))

end HtrRequestList
end InitECandidate.Solver.Input.CurrentHash

#print axioms InitECandidate.Solver.Input.CurrentHash.HtrRequestList.preserves
