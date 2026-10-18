import InitECandidate.Solver.MutableTable.DeleteScanLocals

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual final empty-byte iteration increments j, breaks and exits
the while, consuming its single loop clock and leaving memory intact. -/
theorem scan_end (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (hole bits start cursor : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (locals : ScanLocals source kind plan hole (Probe.slot plan.capacity start cursor))
    (empty : Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 (Probe.slot plan.capacity start (cursor + 1))) = some 0)
    (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source loop = (none, WitnessRadix.QueryBranch.bind (decClockHOLFinite source) "j"
      (BitVec.ofNat 64 (Probe.slot plan.capacity start (cursor + 1)))) := by
  classical
  let entry := decClockHOLFinite source
  let next := Probe.slot plan.capacity start (cursor + 1)
  let advanced := WitnessRadix.QueryBranch.bind entry "j" (BitVec.ofNat 64 next)
  have entryLocals := ScanLocals.of_locals source entry kind plan hole _ locals rfl
  have advancedLocals := ScanLocals.advance entry kind plan hole _ next entryLocals
  have incrementRun : evaluateHOLFiniteState entry incrementJ = (none, advanced) := by
    simpa only [Find.pathIndex, ← power] using increment_j_execute entry bits start cursor small
      (by simpa only [power] using entryLocals.cap) (by simpa only [Find.pathIndex, ← power] using entryLocals.slot)
  have test := empty_test_read advanced kind plan _ 0 advancedLocals.used advancedLocals.slot empty
  have breakRun : evaluateHOLFiniteState advanced (.ite emptyTest .break .skip) = (some .break, advanced) := by
    rw [evaluateHOLFiniteState_ite]
    change evalHOLExact advanced.toExact emptyTest = _ at test
    rw [test]
    simp
  have bodyRun : evaluateHOLFiniteState entry loopBody = (some .break, advanced) := by
    rw [loopBody, StateSteps.next_sequence entry advanced incrementJ _ incrementRun (Nat.le_refl _),
      StateSteps.stopped_sequence advanced advanced (.ite emptyTest .break .skip) hashCall .break breakRun (Nat.le_refl _)]
  rw [loop, evaluateHOLFiniteState_while_total]
  simp only [evalHOLFinite, evalHOLExact, show (1#64 : BitVec 64) ≠ 0#64 from by decide, ↓reduceIte,
    if_neg (show source.clock ≠ 0 from by omega)]
  rw [bodyRun, StateSteps.fixed_clock entry advanced (some .break) (Nat.le_refl _)]
  simp [advanced, entry, next]

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.scan_end
