import InitECandidate.Solver.GasBudget.McopyCopies
import InitECandidate.Solver.WitnessRadix.AllocationContinuing

namespace InitECandidate.Solver.GasBudget.Mcopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 10000 in
theorem allocation_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch src dst n mark : BitVec 64)
    (view : MemoryExtend.View source frame base length capacity pointer scratch)
    (srcLocal : source.locals.lookup (ofString "s") = some (.val (.word src)))
    (dstLocal : source.locals.lookup (ofString "d") = some (.val (.word dst)))
    (nLocal : source.locals.lookup (ofString "n") = some (.val (.word n)))
    (markLocal : source.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)))
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (baseLower : 2701131776 ≤ base.toNat) (scratchUpper : scratch.toNat ≤ 33806089496)
    (markAligned : mark.toNat % 8 = 0) (markUpper : mark.toNat ≤ 33806089496)
    (headerBefore : frame.toNat + 280 ≤ mark.toNat)
    (sourceRange : src.toNat + n.toNat ≤ length.toNat) (destinationRange : dst.toNat + n.toNat ≤ length.toNat)
    (normal : evaluateHOLFiniteState source afterMark = (none, post)) :
    mark.toNat + n.toNat ≤ 33806089496 ∧
      copyPrice base src dst mark n.toNat + 1 ≤ source.clock ∧
      post.clock = source.clock - (copyPrice base src dst mark n.toNat + 1) ∧
      MemoryExtend.View post frame base length capacity pointer scratch ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) ∧
      (∀ query, Arenas.Outside base scratch query → CopyGeneral.Away mark query n.toNat → post.memory query = source.memory query) := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "n"] = some (PersistentAlloc.values n) := by
    simp [PersistentAlloc.values, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, nLocal]
  obtain ⟨room, positive, inner, run, scopeEq⟩ := PersistentAlloc.call_continuing source post "tmp" [localVar "n"] copies mark n args
    (alloc_code source.code view.installed) (MemoryExtend.trap_code source.code view.installed) heapGlobal markUpper normal
  let ready := bind (PersistentAlloc.post {source with clock := source.clock - 1} mark n) "tmp" mark
  have readyView : MemoryExtend.View ready frame base length capacity pointer scratch :=
    (view.with_heap (PersistentAlloc.rounded mark n)).after_erase rfl
  have other (key : String) (different : ofString "tmp" ≠ ofString key) : ready.locals.lookup (ofString key) = source.locals.lookup (ofString key) :=
    bind_lookup_other _ "tmp" key _ different
  have readyTmp : ready.locals.lookup (ofString "tmp") = some (.val (.word mark)) := bind_lookup_same _ _ _
  have readyHeap : ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (PersistentAlloc.rounded mark n))) := by
    simp [ready, WitnessRadix.QueryBranch.bind, setVarHOLFinite, PersistentAlloc.post, HolFiniteMapExact.update, FUPDATE]
  have readyDomain : ready.memaddrs = InitE.ordinaryDomain := domain
  have markLower : 2701131776 ≤ mark.toNat := by
    have cursor := view.cursor
    have order := BitVec.le_def.mp view.ordered
    have frameAbove := view.frameAbove
    omega
  have temporary : AllocatedBytes.Arena mark n.toNat := ⟨markLower, room⟩
  obtain ⟨funded, clock, innerView, locals, globals, away⟩ := copies_normal ready inner frame base length capacity pointer scratch src dst n mark
    (PersistentAlloc.rounded mark n) readyView
    ((other "s" (by decide)).trans srcLocal) ((other "d" (by decide)).trans dstLocal) ((other "n" (by decide)).trans nLocal)
    readyTmp ((other "mark" (by decide)).trans markLocal) readyHeap readyDomain baseLower scratchUpper temporary markAligned headerBefore sourceRange destinationRange run
  change copyPrice base src dst mark n.toNat ≤ source.clock - 1 at funded
  change inner.clock = source.clock - 1 - copyPrice base src dst mark n.toNat at clock
  refine ⟨room, by omega, ?_, innerView.after_erase (by rw [scopeEq]; rfl), ?_, ?_⟩
  · rw [scopeEq]
    change inner.clock = _
    rw [clock]
    omega
  · rw [scopeEq]
    change inner.globals.lookup _ = _
    rw [globals]
    simp [Input.HeapScope.releasePost, HolFiniteMapExact.update, FUPDATE]
  · intro query outside heapAway
    rw [scopeEq]
    exact away query outside heapAway

end InitECandidate.Solver.GasBudget.Mcopy

#print axioms InitECandidate.Solver.GasBudget.Mcopy.allocation_normal
