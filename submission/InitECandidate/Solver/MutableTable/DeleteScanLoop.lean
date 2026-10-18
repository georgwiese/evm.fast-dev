import InitECandidate.Solver.MutableTable.DeleteScanStep
import InitECandidate.Solver.MutableTable.DeleteScanEnd

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def scanPrice (kind : KeyHash.Kind) : Nat := KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 2

/-- Complete original deletion scan through an unchanged used-byte prefix.
Each occupied iteration pays for the actual hash, optional copy and while;
the final empty iteration pays one while clock. The physical model, header,
nonlocal state and all locals other than i/j are preserved as specified. -/
theorem scan_loop (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (bits start : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits) (startInside : start < plan.capacity)
    (count : Nat) (deleted : Fin count)
    (remaining : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (cursor : Nat) (entries : Fin count → Nat) (hole : Nat)
    (stopInside : cursor + remaining + 1 < plan.capacity)
    (pending : Pending source kind plan count deleted entries hole)
    (frontier : Frontier plan.capacity start cursor hole)
    (locals : ScanLocals source kind plan hole (Probe.slot plan.capacity start cursor))
    (occupied : ∀ rank, cursor < rank → rank < cursor + remaining + 1 →
      Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 (Probe.slot plan.capacity start rank)) = some 1)
    (empty : Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 (Probe.slot plan.capacity start (cursor + remaining + 1))) = some 0)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 count))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : scanPrice kind * remaining + 1 ≤ source.clock) :
    ∃ paid memory target nextEntries nextHole, paid ≤ scanPrice kind * remaining + 1 ∧
      evaluateHOLFiniteState source loop = (none, target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - paid} ∧
      ScanLocals target kind plan nextHole (Probe.slot plan.capacity start (cursor + remaining + 1)) ∧
      Pending target kind plan count deleted nextEntries nextHole ∧
      Frontier plan.capacity start (cursor + remaining + 1) nextHole ∧
      MemoryModel.Header memory kind plan (BitVec.ofNat 64 count) ∧
      (∀ query < plan.capacity, Find.usedByte {source with memory := memory} (parameters kind plan 0#64) (BitVec.ofNat 64 query) =
        Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 query)) ∧
      (∀ name : String, ofString "i" ≠ ofString name → ofString "j" ≠ ofString name →
        target.locals.lookup (ofString name) = source.locals.lookup (ofString name)) ∧
      TableFootprint.Frame source.memory memory kind plan := by
  classical
  induction remaining generalizing source cursor entries hole with
  | zero =>
    let target := WitnessRadix.QueryBranch.bind (decClockHOLFinite source) "j" (BitVec.ofNat 64 (Probe.slot plan.capacity start (cursor + 1)))
    have actual := scan_end source kind plan hole bits start cursor small power locals (by simpa only [Nat.add_zero] using empty) (by simpa only [Nat.mul_zero, Nat.zero_add] using enough)
    refine ⟨1, source.memory, target, entries, hole, by simp, actual, rfl, ?_, ?_, ?_, header, ?_, ?_, TableFootprint.Frame.refl _ _ _⟩
    · exact ScanLocals.advance _ kind plan hole _ _ (ScanLocals.of_locals source _ kind plan hole _ locals rfl)
    · exact Pending.of_fields source target kind plan count deleted entries hole pending rfl rfl rfl
    · exact frontier_after_choice plan.capacity start cursor hole hole frontier (Or.inl rfl)
    · intro query inside; rfl
    · intro name awayI awayJ
      exact bind_lookup_other _ "j" name _ awayJ
  | succ remaining ih =>
    have funded : scanPrice kind * remaining + scanPrice kind + 1 ≤ source.clock := by
      simpa only [Nat.mul_add, Nat.mul_one] using enough
    have positive : source.clock ≠ 0 := by unfold scanPrice at funded; omega
    let entry := decClockHOLFinite source
    have entryLocals := ScanLocals.of_locals source entry kind plan hole _ locals rfl
    have entryPending := Pending.of_fields source entry kind plan count deleted entries hole pending rfl rfl rfl
    obtain ⟨paid, memory, nextEntries, nextHole, bounded, bodyRun, nextPending, nextFrontier, nextHeader, stable, firstFootprint⟩ :=
      scan_step entry kind plan valid domain little count deleted entries hole entryPending bits start cursor small power startInside (by omega) frontier entryLocals
        (occupied (cursor + 1) (by omega) (by omega)) header hashCode copyCode
        (by change KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ≤ source.clock - 1; unfold scanPrice at funded; omega)
    let advanced := WitnessRadix.QueryBranch.bind entry "j" (BitVec.ofNat 64 (Probe.slot plan.capacity start (cursor + 1)))
    let nextState := WitnessRadix.QueryBranch.bind {advanced with memory := memory, clock := advanced.clock - paid} "i" (BitVec.ofNat 64 nextHole)
    have nextLocals : ScanLocals nextState kind plan nextHole (Probe.slot plan.capacity start (cursor + 1)) :=
      ScanLocals.after_hash advanced kind plan hole _ nextHole (ScanLocals.advance entry kind plan hole _ _ entryLocals) memory paid
    have stepBound : paid + 1 ≤ scanPrice kind := by unfold scanPrice; omega
    have nextEnough : scanPrice kind * remaining + 1 ≤ nextState.clock := by
      change scanPrice kind * remaining + 1 ≤ source.clock - 1 - paid
      omega
    have sum : cursor + 1 + remaining + 1 = cursor + (remaining + 1) + 1 := by omega
    obtain ⟨restPaid, finalMemory, target, finalEntries, finalHole, restBound, restRun, restFrame, finalLocals, finalPending, finalFrontier, finalHeader, restStable, restOther, restFootprint⟩ :=
      ih nextState domain little (cursor + 1) nextEntries nextHole (by omega) nextPending nextFrontier nextLocals
        (by
          intro rank lower upper
          exact (stable _ (Nat.mod_lt _ valid.positive)).trans (occupied rank (by omega) (by omega)))
        (by
          have here : Find.usedByte entry (parameters kind plan 0#64) (BitVec.ofNat 64 (Probe.slot plan.capacity start (cursor + (remaining + 1) + 1))) = some 0 := empty
          exact (stable (Probe.slot plan.capacity start (cursor + 1 + remaining + 1)) (Nat.mod_lt _ valid.positive)).trans (by simpa only [sum] using here))
        nextHeader hashCode copyCode nextEnough
    have totalBound : 1 + paid + restPaid ≤ scanPrice kind * (remaining + 1) + 1 := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have frameEq : emptyLocalsHOLFinite {nextState with memory := finalMemory, clock := nextState.clock - restPaid} =
        emptyLocalsHOLFinite {source with memory := finalMemory, clock := source.clock - (1 + paid + restPaid)} := by
      change emptyLocalsHOLFinite {source with memory := finalMemory, clock := source.clock - 1 - paid - restPaid} = _
      have subtract : source.clock - 1 - paid - restPaid = source.clock - (1 + paid + restPaid) := by omega
      rw [subtract]
    refine ⟨1 + paid + restPaid, finalMemory, target, finalEntries, finalHole, totalBound, ?_, restFrame.trans frameEq,
      by simpa only [sum] using finalLocals, finalPending, by simpa only [sum] using finalFrontier, finalHeader, ?_, ?_, TableFootprint.Frame.trans source.memory memory finalMemory kind plan firstFootprint restFootprint⟩
    · rw [loop, evaluateHOLFiniteState_while_total]
      simp only [evalHOLFinite, evalHOLExact, if_neg positive]
      change evaluateHOLFiniteState entry loopBody = (none, nextState) at bodyRun
      rw [bodyRun, StateSteps.fixed_clock entry nextState none (by change source.clock - 1 - paid ≤ source.clock - 1; omega)]
      simpa [loop] using restRun
    · intro query inside
      exact (restStable query inside).trans (stable query inside)
    · intro name awayI awayJ
      exact (restOther name awayI awayJ).trans ((bind_lookup_other _ "i" name _ awayI).trans (bind_lookup_other _ "j" name _ awayJ))

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.scan_loop
