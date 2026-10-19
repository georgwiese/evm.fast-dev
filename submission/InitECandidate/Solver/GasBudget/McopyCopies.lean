import InitECandidate.Solver.GasBudget.McopyCopyProgram
import InitECandidate.Solver.WitnessRadix.AllocatedAwayBelow
import InitECandidate.Solver.Input.ControlContinue

namespace InitECandidate.Solver.GasBudget.Mcopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def copyPrice (base src dst mark : BitVec 64) (n : Nat) : Nat :=
  CopyGeneral.cost (base + src) mark n + CopyGeneral.cost mark (base + dst) n + 3

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 10000 in
theorem copies_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch src dst n mark heap : BitVec 64)
    (view : MemoryExtend.View source frame base length capacity pointer scratch)
    (srcLocal : source.locals.lookup (ofString "s") = some (.val (.word src)))
    (dstLocal : source.locals.lookup (ofString "d") = some (.val (.word dst)))
    (nLocal : source.locals.lookup (ofString "n") = some (.val (.word n)))
    (tmpLocal : source.locals.lookup (ofString "tmp") = some (.val (.word mark)))
    (markLocal : source.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (baseLower : 2701131776 ≤ base.toNat) (scratchUpper : scratch.toNat ≤ 33806089496)
    (temporary : AllocatedBytes.Arena mark n.toNat) (markAligned : mark.toNat % 8 = 0)
    (headerBefore : frame.toNat + 280 ≤ mark.toNat)
    (sourceRange : src.toNat + n.toNat ≤ length.toNat) (destinationRange : dst.toNat + n.toNat ≤ length.toNat)
    (normal : evaluateHOLFiniteState source copies = (none, post)) :
    copyPrice base src dst mark n.toNat ≤ source.clock ∧
      post.clock = source.clock - copyPrice base src dst mark n.toNat ∧
      MemoryExtend.View post frame base length capacity pointer scratch ∧
      post.locals = source.locals ∧
      post.globals = (Input.HeapScope.releasePost source mark).globals ∧
      (∀ query, Arenas.Outside base scratch query → CopyGeneral.Away mark query n.toNat → post.memory query = source.memory query) := by
  have firstSafe : Input.LocalPrefix (ofString "n") firstCopy := .call none _ _ (by simp)
  obtain ⟨first, firstRun, remainingRun, retained⟩ := firstSafe.control_continue source post (.seq secondCopy release) none .next normal
  have baseRead := frame_read source frame 24#64 base view.ev (view.mapped 24 (by simp)) view.baseCell
  have firstArgs : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [localVar "tmp", copyAddress "s", localVar "n"] = some (CopyGeneral.values mark (base + src) n.toNat) := by
    simp only [eval] at baseRead
    simp [CopyGeneral.values, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, copyAddress,
      tmpLocal, srcLocal, nLocal, baseRead, BitVec.ofNat_toNat, BitVec.setWidth_eq, valueIsWord, valueWord, wordOpHOL, wordOp]
  have srcArena := view.span_arena src n.toNat sourceRange baseLower scratchUpper
  have dstArena := view.span_arena dst n.toNat destinationRange baseLower scratchUpper
  have small : n.toNat + 32 < 2 ^ 64 := by have bound := temporary.upper; omega
  obtain ⟨firstFits, firstBound, firstEq⟩ := CopyGeneral.call_normal source first _ (base + src) mark n.toNat firstArgs
    (copy_code source.code view.installed) (AllocatedBytes.copy_mapped source _ _ _ domain srcArena temporary) small firstRun
  have firstAway (query : BitVec 64) (below : query.toNat < mark.toNat) : first.memory query = source.memory query := by
    rw [firstEq]
    exact CopyGeneral.call_memory_away source (base + src) mark query n.toNat (temporary.away_below mark query n.toNat markAligned below)
  have headerBelow (offset : Nat) (inside : offset < 280) : (frame + BitVec.ofNat 64 offset).toNat < mark.toNat := by
    have number : (BitVec.ofNat 64 offset).toNat = offset := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have sum := BitVec.toNat_add_of_lt (show frame.toNat + (BitVec.ofNat 64 offset).toNat < 2 ^ 64 by rw [number]; have bound := view.frameFits; omega)
    rw [sum, number]
    omega
  have firstView : MemoryExtend.View first frame base length capacity pointer scratch := by
    have fields : Input.LocalEffects.erase first = Input.LocalEffects.erase {source with memory := first.memory} := by rw [firstEq]; rfl
    exact (view.with_memory _ ((firstAway _ (headerBelow 24 (by decide))).trans view.baseCell)
      ((firstAway _ (headerBelow 32 (by decide))).trans view.lengthCell)
      ((firstAway _ (headerBelow 40 (by decide))).trans view.capacityCell)).after_erase fields
  have secondSafe : Input.LocalPrefix (ofString "n") secondCopy := .call none _ _ (by simp)
  obtain ⟨second, secondRun, releaseRun, saved⟩ := secondSafe.control_continue first post release none .next remainingRun
  have secondBaseRead := frame_read first frame 24#64 base firstView.ev (firstView.mapped 24 (by simp)) firstView.baseCell
  have secondArgs : evalListHOLFinite first (h := fun address => Classical.propDecidable (first.memaddrs address))
      [copyAddress "d", localVar "tmp", localVar "n"] = some (CopyGeneral.values (base + dst) mark n.toNat) := by
    simp only [eval] at secondBaseRead
    have nCell : first.locals.lookup (ofString "n") = some (.val (.word n)) := by rw [firstEq]; exact nLocal
    have dCell : first.locals.lookup (ofString "d") = some (.val (.word dst)) := by rw [firstEq]; exact dstLocal
    have tmpCell : first.locals.lookup (ofString "tmp") = some (.val (.word mark)) := by rw [firstEq]; exact tmpLocal
    simp [CopyGeneral.values, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, copyAddress,
      tmpCell, dCell, nCell, secondBaseRead, BitVec.ofNat_toNat, BitVec.setWidth_eq, valueIsWord, valueWord, wordOpHOL, wordOp]
  have firstDomain : first.memaddrs = InitE.ordinaryDomain := by rw [firstEq]; exact domain
  obtain ⟨secondFits, secondBound, secondEq⟩ := CopyGeneral.call_normal first second _ mark (base + dst) n.toNat secondArgs
    (copy_code first.code firstView.installed) (AllocatedBytes.copy_mapped first _ _ _ firstDomain temporary dstArena) small secondRun
  have secondAway (query : BitVec 64) (outside : Arenas.Outside base scratch query) : second.memory query = first.memory query := by
    rw [secondEq]
    exact CopyGeneral.call_memory_away first mark (base + dst) query n.toNat (firstView.copy_away dst n.toNat destinationRange query outside)
  have secondView : MemoryExtend.View second frame base length capacity pointer scratch := by
    have fields : Input.LocalEffects.erase second = Input.LocalEffects.erase {first with memory := second.memory} := by rw [secondEq]; rfl
    exact (firstView.with_memory _ ((secondAway _ (view.header_outside 24 (by decide))).trans firstView.baseCell)
      ((secondAway _ (view.header_outside 32 (by decide))).trans firstView.lengthCell)
      ((secondAway _ (view.header_outside 40 (by decide))).trans firstView.capacityCell)).after_erase fields
  have releaseArgs : evalListHOLFinite second (h := fun address => Classical.propDecidable (second.memaddrs address)) [localVar "mark"] = some [.val (.word mark)] := by
    have cell : second.locals.lookup (ofString "mark") = some (.val (.word mark)) := by rw [secondEq, firstEq]; exact markLocal
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, cell]
  have heapCell : second.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by rw [secondEq, firstEq]; exact heapGlobal
  have releaseFits := (Input.CallNormal.ignored_data second post (ofString "heap_release") [localVar "mark"] releaseRun).1
  have actualRelease := Input.HeapScope.release_call_execute second mark heap [localVar "mark"] releaseArgs heapCell
    (release_code second.code secondView.installed) releaseFits
  have postEq := congrArg Prod.snd (releaseRun.symm.trans actualRelease)
  change post = Input.HeapScope.releasePost {second with clock := second.clock - 1} mark at postEq
  have firstClock : first.clock = source.clock - (CopyGeneral.cost (base + src) mark n.toNat + 1) := by rw [firstEq]; rfl
  have secondClock : second.clock = first.clock - (CopyGeneral.cost mark (base + dst) n.toNat + 1) := by rw [secondEq]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [secondClock, firstClock] at releaseFits
    rw [firstClock] at secondFits
    unfold copyPrice
    omega
  · rw [postEq]
    change second.clock - 1 = _
    rw [secondClock, firstClock]
    unfold copyPrice
    omega
  · rw [postEq]
    exact (secondView.with_heap mark).after_erase rfl
  · rw [postEq, secondEq, firstEq]; rfl
  · rw [postEq, secondEq, firstEq]; rfl
  · intro query outside away
    rw [postEq]
    change second.memory query = _
    rw [secondAway query outside, firstEq]
    exact CopyGeneral.call_memory_away source (base + src) mark query n.toNat away

end InitECandidate.Solver.GasBudget.Mcopy

#print axioms InitECandidate.Solver.GasBudget.Mcopy.copies_normal
