import InitECandidate.Solver.GasBudget.McopyAllocation
import InitECandidate.Solver.GasBudget.MemoryCostContinuing
import InitECandidate.Solver.Input.HeapMarkContinuing

namespace InitECandidate.Solver.GasBudget.Mcopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 10000 in
theorem copy_branch_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch n mark : BitVec 64) (src dst : U256Value.Words)
    (view : MemoryExtend.View source frame base length capacity pointer scratch)
    (srcLocal : source.locals.lookup (ofString "src") = some (U256Value.tuple src))
    (dstLocal : source.locals.lookup (ofString "dst") = some (U256Value.tuple dst))
    (nLocal : source.locals.lookup (ofString "n") = some (.val (.word n)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)))
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (baseLower : 2701131776 ≤ base.toNat) (scratchUpper : scratch.toNat ≤ 33806089496)
    (markAligned : mark.toNat % 8 = 0) (markUpper : mark.toNat ≤ 33806089496)
    (headerBefore : frame.toNat + 280 ≤ mark.toNat)
    (sourceRange : (SatWord.resultWord src).toNat + n.toNat ≤ length.toNat)
    (destinationRange : (SatWord.resultWord dst).toNat + n.toNat ≤ length.toNat)
    (normal : evaluateHOLFiniteState source copyBranch = (none, post)) :
    mark.toNat + n.toNat ≤ 33806089496 ∧
      copyPrice base (SatWord.resultWord src) (SatWord.resultWord dst) mark n.toNat + 4 ≤ source.clock ∧
      post.clock = source.clock - (copyPrice base (SatWord.resultWord src) (SatWord.resultWord dst) mark n.toNat + 4) ∧
      MemoryExtend.View post frame base length capacity pointer scratch ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) ∧
      (∀ query, Arenas.Outside base scratch query → CopyGeneral.Away mark query n.toNat → post.memory query = source.memory query) := by
  have dstRead : eval source (localVar "dst") = some (U256Value.tuple dst) := by simp [eval, localVar, evalHOLExact, toExact, dstLocal]
  obtain ⟨paidD, first, firstPost, positiveD, boundD, fitsD, firstEq, firstFields, firstRun, firstScope⟩ :=
    MemoryCostCalls.continuing .sat source post "d" (localVar "dst") afterDestination dst view.installed dstRead normal
  have paidDEq : paidD = 1 := by change paidD ≤ 1 at boundD; omega
  subst paidD
  have firstView := view.after_erase firstFields
  have firstSrc := (Input.KnownUnaryPrefix.lookup_other firstEq "src" (by decide)).trans srcLocal
  have firstD := Input.KnownUnaryPrefix.lookup_same firstEq
  have firstN := (Input.KnownUnaryPrefix.lookup_other firstEq "n" (by decide)).trans nLocal
  have srcRead : eval first (localVar "src") = some (U256Value.tuple src) := by simp [eval, localVar, evalHOLExact, toExact, firstSrc]
  obtain ⟨paidS, second, secondPost, positiveS, boundS, fitsS, secondEq, secondFields, secondRun, secondScope⟩ :=
    MemoryCostCalls.continuing .sat first firstPost "s" (localVar "src") afterSource src firstView.installed srcRead firstRun
  have paidSEq : paidS = 1 := by change paidS ≤ 1 at boundS; omega
  subst paidS
  have secondView := firstView.after_erase secondFields
  have secondS := Input.KnownUnaryPrefix.lookup_same secondEq
  have secondD := (Input.KnownUnaryPrefix.lookup_other secondEq "d" (by decide)).trans firstD
  have secondN := (Input.KnownUnaryPrefix.lookup_other secondEq "n" (by decide)).trans firstN
  have heapCell : second.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) := by rw [secondEq, firstEq]; exact heapGlobal
  obtain ⟨markFits, inner, allocationRun, markScope⟩ := Input.HeapScope.mark_call_continuing second secondPost mark "mark" afterMark heapCell
    (mark_code second.code secondView.installed) secondRun
  let ready := bind {second with clock := second.clock - 1} "mark" mark
  have readyView : MemoryExtend.View ready frame base length capacity pointer scratch := secondView.after_erase rfl
  have other (key : String) (different : ofString "mark" ≠ ofString key) : ready.locals.lookup (ofString key) = second.locals.lookup (ofString key) := bind_lookup_other _ "mark" key _ different
  have readyDomain : ready.memaddrs = InitE.ordinaryDomain := by change second.memaddrs = _; rw [secondEq, firstEq]; exact domain
  obtain ⟨room, funded, clock, innerView, finalHeap, away⟩ := allocation_normal ready inner frame base length capacity pointer scratch
    (SatWord.resultWord src) (SatWord.resultWord dst) n mark readyView
    ((other "s" (by decide)).trans secondS) ((other "d" (by decide)).trans secondD) ((other "n" (by decide)).trans secondN)
    (bind_lookup_same _ _ _) heapCell readyDomain baseLower scratchUpper markAligned markUpper headerBefore sourceRange destinationRange allocationRun
  have firstClock : first.clock = source.clock - 1 := by rw [firstEq]; rfl
  have secondClock : second.clock = first.clock - 1 := by rw [secondEq]; rfl
  have scopeFields : Input.LocalEffects.erase post = Input.LocalEffects.erase inner := by rw [firstScope, secondScope, markScope]; rfl
  have scopeClock : post.clock = inner.clock := by rw [firstScope, secondScope, markScope]; rfl
  have readyMemory : ready.memory = source.memory := by change second.memory = _; rw [secondEq, firstEq]; rfl
  change copyPrice base (SatWord.resultWord src) (SatWord.resultWord dst) mark n.toNat + 1 ≤ second.clock - 1 at funded
  change inner.clock = second.clock - 1 - (copyPrice base (SatWord.resultWord src) (SatWord.resultWord dst) mark n.toNat + 1) at clock
  refine ⟨room, ?_, ?_, innerView.after_erase scopeFields, ?_, ?_⟩
  · rw [secondClock, firstClock] at funded
    rw [firstClock] at fitsS
    omega
  · rw [scopeClock, clock, secondClock, firstClock]
    omega
  · rw [firstScope, secondScope, markScope]
    exact finalHeap
  · intro query outside heapAway
    rw [Input.LocalEffects.memory_of_erase inner post scopeFields, away query outside heapAway, readyMemory]

end InitECandidate.Solver.GasBudget.Mcopy

#print axioms InitECandidate.Solver.GasBudget.Mcopy.copy_branch_normal
