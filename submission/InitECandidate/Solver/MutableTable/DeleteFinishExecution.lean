import InitECandidate.Solver.MutableTable.DeleteFinishModel
import InitECandidate.Solver.MutableTable.DeleteLastDecision
import InitECandidate.Solver.MutableTable.DeleteScanLocals
import InitECandidate.Solver.MutableTable.ByteStoreExec

namespace InitECandidate.Solver.MutableTable.Delete.Finish
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def tail : ProgHOL 64 := .seq (.ite Delete.lastTest Delete.lastBranch .skip) (.seq Delete.countStore Delete.returnOne)
def afterN : ProgHOL 64 := .dec (ofString "last_pos") .one (.op .sub [localVar "n", .const 1#64]) tail

/-- All final instructions of the unchanged deletion: clear the hole,
read/decrement count, optional actual last-entry swap, count store and return.
These instructions cost no additional source clocks; target pricing remains
a separate obligation. The executed memory establishes the surviving model. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole slot : Nat)
    (pending : Pending source kind plan count deleted entries hole) (locals : ScanLocals source kind plan hole slot)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (deletedLocal : source.locals.lookup (ofString "deleted_pos") = some (.val (.word (BitVec.ofNat 64 deleted.val))))
    (oldHeader : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 count)) :
    ∃ target, evaluateHOLFiniteState source Delete.afterLoop = (some (.returned (.val (.word 1#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory source.memory plan deleted entries hole} ∧
      MemoryModel.Header target.memory kind plan (BitVec.ofNat 64 (count - 1)) ∧
      MemoryModel.Occupied target kind plan (finalSlots entries deleted) := by
  let cleared := {source with memory := clearedMemory source.memory plan hole}
  let numbered := WitnessRadix.QueryBranch.bind cleared "n" (BitVec.ofNat 64 count)
  let entered := WitnessRadix.QueryBranch.bind numbered "last_pos" (BitVec.ofNat 64 (count - 1))
  let swapped := {entered with memory := swapMemory cleared.memory plan deleted entries}
  let counted := {entered with memory := memory source.memory plan deleted entries hole}
  have holeExtent := used_offset_inside kind plan hole pending.holeInside
  have clearAddress : eval source (.op .add [localVar "used", localVar "i"]) = some (.val (.word (cell plan .used 0 + BitVec.ofNat 64 hole))) := by
    simp [eval, localVar, evalHOLExact, evalListHOLExact, toExact, locals.used, locals.hole, valueIsWord, valueWord, wordOpHOL, wordOp]
  have mappedHole : source.memaddrs (panByteAlignHOL (width := 64) (cell plan .used 0 + BitVec.ofNat 64 hole)) := by
    rw [domain, constant_cell]
    exact byte_mapped kind plan valid .used hole holeExtent
  have clearRun : evaluateHOLFiniteState source Delete.clearUsed = (none, cleared) :=
    ByteStore.execute source _ (.const 0#64) _ 0 clearAddress rfl mappedHole little
  have countAddress : cell plan .header 0 + 24#64 = cell plan .header 24 := constant_cell plan .header 24
  have mappedCount : source.memaddrs (cell plan .header 24) := by
    rw [domain]
    exact mapped kind plan valid .header 24 (by change 24 < 72; decide) (by decide)
  have keptCount : cleared.memory (cell plan .header 24) = .word (BitVec.ofNat 64 count) :=
    (cleared_pool_away source.memory kind plan valid hole pending.holeInside .header (by decide) 24 (by change 24 < 72; decide)).trans (oldHeader 24 _ (by simp [MemoryModel.headerEntries]))
  have countRead : eval cleared (Find.tableLoad 24#64) = some (.val (.word (BitVec.ofNat 64 count))) := by
    have hereT : cleared.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) := tableLocal
    have hereMapped : cleared.memaddrs (cell plan .header 24) := mappedCount
    simp [eval, Find.tableLoad, localVar, evalHOLExact, evalListHOLExact, toExact, hereT, valueIsWord, valueWord, wordOpHOL, wordOp, countAddress,
      memLoadHOLExact, isWfShapeExactHOL, hereMapped, keptCount]
  have countPositive : 0 < count := by have := deleted.isLt; omega
  have subtract : BitVec.ofNat 64 count - 1#64 = BitVec.ofNat 64 (count - 1) :=
    BitVec.ofNat_sub_ofNat_of_le count 1 (by decide) countPositive
  have nLocal : numbered.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 count))) := bind_lookup_same _ _ _
  have lastRead : eval numbered (.op .sub [localVar "n", .const 1#64]) = some (.val (.word (BitVec.ofNat 64 (count - 1)))) := by
    simp [eval, localVar, evalHOLExact, evalListHOLExact, toExact, nLocal, valueIsWord, valueWord, wordOpHOL, wordOp, subtract]
  have swapLocals : SwapLocals entered plan deleted.val (count - 1) :=
    ⟨(bind_lookup_other _ "last_pos" "order" _ (by decide)).trans ((bind_lookup_other _ "n" "order" _ (by decide)).trans locals.order),
      (bind_lookup_other _ "last_pos" "order_pos" _ (by decide)).trans ((bind_lookup_other _ "n" "order_pos" _ (by decide)).trans locals.position),
      (bind_lookup_other _ "last_pos" "deleted_pos" _ (by decide)).trans ((bind_lookup_other _ "n" "deleted_pos" _ (by decide)).trans deletedLocal),
      bind_lookup_same _ _ _⟩
  have swapRun : evaluateHOLFiniteState entered (.ite Delete.lastTest Delete.lastBranch .skip) = (none, swapped) :=
    last_swap_execute entered kind plan valid domain count deleted entries pending.room swapLocals
      (fun swap => pending.inside _ (last_active deleted swap))
      (by
        intro swap
        exact (cleared_pool_away source.memory kind plan valid hole pending.holeInside .order (by decide) (8 * (count - 1))
          (by change 8 * (count - 1) < 8 * plan.capacity; have := pending.room; omega)).trans (pending.order _ (last_active deleted swap)))
  have swappedT : swapped.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) :=
    (bind_lookup_other _ "last_pos" "t" _ (by decide)).trans ((bind_lookup_other _ "n" "t" _ (by decide)).trans tableLocal)
  have storeAddress : eval swapped (.op .add [localVar "t", .const 24#64]) = some (.val (.word (cell plan .header 24))) := by
    simp [eval, localVar, evalHOLExact, evalListHOLExact, toExact, swappedT, valueIsWord, valueWord, wordOpHOL, wordOp, countAddress]
  have storeValue : eval swapped (localVar "last_pos") = some (.val (.word (BitVec.ofNat 64 (count - 1)))) := by
    have here : swapped.locals.lookup (ofString "last_pos") = some (.val (.word (BitVec.ofNat 64 (count - 1)))) := swapLocals.last
    simp only [eval, localVar, evalHOLExact, toExact, here]
  have stored := StoreWord.execute swapped (.op .add [localVar "t", .const 24#64]) (localVar "last_pos") _ _ storeAddress storeValue mappedCount
  have countedEq : {swapped with memory := StoreWord.put swapped.memory (cell plan .header 24) (BitVec.ofNat 64 (count - 1))} = counted := by
    change {entered with memory := StoreWord.put (swapMemory (clearedMemory source.memory plan hole) plan deleted entries) (cell plan .header 24) (BitVec.ofNat 64 (count - 1))} = counted
    rw [← memory_eq_count source.memory plan deleted entries hole]
  have storeRun : evaluateHOLFiniteState swapped Delete.countStore = (none, counted) := by simpa only [Delete.countStore, countedEq] using stored
  have returnRun : evaluateHOLFiniteState counted Delete.returnOne = (some (.returned (.val (.word 1#64))), emptyLocalsHOLFinite counted) := by
    simp [Delete.returnOne, evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
  have tailRun : evaluateHOLFiniteState entered tail = (some (.returned (.val (.word 1#64))), emptyLocalsHOLFinite counted) := by
    rw [tail, StateSteps.next_sequence entered swapped _ _ swapRun (Nat.le_refl _),
      StateSteps.next_sequence swapped counted Delete.countStore Delete.returnOne storeRun (Nat.le_refl _), returnRun]
  have lastRun := Input.ScalarScope.declare_execute numbered _ "last_pos" (.op .sub [localVar "n", .const 1#64]) (BitVec.ofNat 64 (count - 1)) tail _ lastRead tailRun
  have nRun := Input.ScalarScope.declare_execute cleared _ "n" (Find.tableLoad 24#64) (BitVec.ofNat 64 count) afterN _ countRead lastRun
  let target := restore cleared "n" (restore numbered "last_pos" (emptyLocalsHOLFinite counted))
  refine ⟨target, ?_, rfl, header source kind plan valid count deleted entries hole pending oldHeader, ?_⟩
  · change evaluateHOLFiniteState source (.seq Delete.clearUsed (.dec (ofString "n") .one (Find.tableLoad 24#64) afterN)) = _
    rw [StateSteps.next_sequence source cleared Delete.clearUsed _ clearRun (Nat.le_refl _)]
    exact nRun
  · exact MemoryModel.Occupied.of_fields _ target kind plan _ (occupied source kind plan valid domain little count deleted entries hole pending) rfl rfl rfl

end InitECandidate.Solver.MutableTable.Delete.Finish

#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.execute
