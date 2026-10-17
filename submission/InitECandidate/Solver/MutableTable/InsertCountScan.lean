import InitECandidate.Solver.MutableTable.InsertScan

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual original raw-insertion scan from physical binary used slots and
an occupied covering list, for every key width. The empty terminator and
strict finite scan are derived, without logical dictionary hypotheses. -/
theorem scan_count_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters)
    (bits start : Nat) (small : bits < 64) (startInside : start < 2 ^ bits)
    (capacity : p.capacity = BitVec.ofNat 64 (2 ^ bits)) (order : List Nat) (room : order.length < 2 ^ bits)
    (binary : ∀ i < 2 ^ bits, Find.usedByte source p (BitVec.ofNat 64 i) = some 0 ∨ Find.usedByte source p (BitVec.ofNat 64 i) = some 1)
    (covered : ∀ i < 2 ^ bits, Find.usedByte source p (BitVec.ofNat 64 i) = some 1 → i ∈ order)
    (locals : Find.Locals source p (Find.pathIndex bits start 0)) (enough : order.length ≤ source.clock) :
    ∃ stop target, stop ≤ order.length ∧
      evaluateHOLFiniteState source loop = (none, target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - stop} ∧
      Find.Locals target p (Find.pathIndex bits start stop) ∧
      Find.usedByte source p (Find.pathIndex bits start stop) = some 0 ∧
      ∀ name, ofString "i" ≠ name → target.locals.lookup name = source.locals.lookup name := by
  obtain ⟨stop, bounded, empty, occupied⟩ := Find.first_empty source p (2 ^ bits) start (Nat.two_pow_pos bits) startInside order room binary covered
  obtain ⟨target, run, frame, finalLocals, others⟩ := scan_prefix source p (Find.pathIndex bits start) 0 stop locals
    (by intro j inside; exact Find.path_advance p bits start j small capacity)
    (by intro j lower upper; exact occupied j (by omega))
    (by simpa only [Nat.zero_add, Find.pathIndex] using empty) (by omega)
  exact ⟨stop, target, bounded, run, frame, by simpa only [Nat.zero_add] using finalLocals, empty, others⟩

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.scan_count_bound
