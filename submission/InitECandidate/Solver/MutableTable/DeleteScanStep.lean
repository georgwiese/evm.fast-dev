import InitECandidate.Solver.MutableTable.DeleteScanLocals
import InitECandidate.Solver.MutableTable.DeleteScanFrontier

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- One occupied iteration of the literal original deletion body, before
the enclosing while-clock. The next-slot/hole distinction follows from the
finite masked frontier; it is not an assumed dictionary correctness fact. -/
theorem scan_step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole)
    (bits start cursor : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (startInside : start < plan.capacity) (nextInside : cursor + 1 < plan.capacity)
    (frontier : Frontier plan.capacity start cursor hole)
    (locals : ScanLocals source kind plan hole (Probe.slot plan.capacity start cursor))
    (used : Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 (Probe.slot plan.capacity start (cursor + 1))) = some 1)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 count))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ≤ source.clock) :
    ∃ paid memory nextEntries nextHole,
      paid ≤ KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ∧
      evaluateHOLFiniteState source loopBody = (none,
        WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid}
          "j" (BitVec.ofNat 64 (Probe.slot plan.capacity start (cursor + 1)))) "i" (BitVec.ofNat 64 nextHole)) ∧
      Pending (WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid}
          "j" (BitVec.ofNat 64 (Probe.slot plan.capacity start (cursor + 1)))) "i" (BitVec.ofNat 64 nextHole)) kind plan count deleted nextEntries nextHole ∧
      Frontier plan.capacity start (cursor + 1) nextHole ∧
      MemoryModel.Header memory kind plan (BitVec.ofNat 64 count) ∧
      (∀ query < plan.capacity, Find.usedByte {source with memory := memory} (parameters kind plan 0#64) (BitVec.ofNat 64 query) =
        Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 query)) := by
  classical
  let next := Probe.slot plan.capacity start (cursor + 1)
  let advanced := WitnessRadix.QueryBranch.bind source "j" (BitVec.ofNat 64 next)
  have advancedLocals := ScanLocals.advance source kind plan hole _ next locals
  have nextBound : next < plan.capacity := Nat.mod_lt _ valid.positive
  have different := frontier_next_different plan.capacity start cursor hole valid.positive startInside nextInside frontier
  obtain ⟨moved, active, selectedSlot, position⟩ := Pending.active source kind plan count deleted entries hole next pending nextBound used different
  have advancedPending := Pending.of_fields source advanced kind plan count deleted entries hole pending rfl rfl rfl
  have incrementRun : evaluateHOLFiniteState source incrementJ = (none, advanced) := by
    simpa only [Find.pathIndex, ← power] using increment_j_execute source bits start cursor small (by simpa only [power] using locals.cap) (by simpa only [Find.pathIndex, ← power] using locals.slot)
  have advancedUsed : Find.usedByte advanced (parameters kind plan 0#64) (BitVec.ofNat 64 next) = some 1 := used
  have test := empty_test_read advanced kind plan _ 1 advancedLocals.used advancedLocals.slot advancedUsed
  have skipRun : evaluateHOLFiniteState advanced (.ite emptyTest .break .skip) = (none, advanced) := by
    rw [evaluateHOLFiniteState_ite]
    change evalHOLExact advanced.toExact emptyTest = _ at test
    rw [test]
    simp
  obtain ⟨value, valueCell⟩ : ∃ value, source.memory (cell plan .values (8 * entries moved)) = .word value := by
    cases stored : source.memory (cell plan .values (8 * entries moved)) with
    | word value => exact ⟨value, rfl⟩
  have moveLocals : Move.Locals advanced kind plan hole (entries moved) := by
    rw [selectedSlot]
    exact advancedLocals.toLocals
  obtain ⟨paid, memory, nextEntries, nextHole, bounded, hashRun, choice, finalPending, finalHeader, stable⟩ :=
    hash_execute advanced kind plan valid domain little count deleted entries hole advancedPending moved active moveLocals value valueCell header advancedLocals.cap hashCode copyCode enough
  refine ⟨paid, memory, nextEntries, nextHole, bounded, ?_, finalPending, ?_, finalHeader, stable⟩
  · rw [loopBody, StateSteps.next_sequence source advanced incrementJ _ incrementRun (Nat.le_refl _),
      StateSteps.next_sequence advanced advanced (.ite emptyTest .break .skip) hashCall skipRun (Nat.le_refl _)]
    exact hashRun
  · exact frontier_after_choice plan.capacity start cursor hole nextHole frontier (by simpa only [selectedSlot] using choice)

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.scan_step
