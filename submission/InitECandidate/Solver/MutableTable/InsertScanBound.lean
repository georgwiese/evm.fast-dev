import InitECandidate.Solver.MutableTable.InsertScan
import InitECandidate.Solver.MutableTable.FindModel32

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem distance_slot (capacity start stop : Nat) (positive : 0<capacity)
    (startInside : start<capacity) (stopInside : stop<capacity) :
    Placement.distance capacity start (Probe.slot capacity start stop)=stop := by
  have inside : Probe.slot capacity start stop<capacity:=Nat.mod_lt _ positive
  apply Probe.slot_injective capacity start _ stop positive startInside
    (Placement.distance_bound capacity start _ positive startInside inside) stopInside
  exact Placement.slot_distance capacity start _ positive startInside inside

/-- The original raw-insertion scan derives its empty slot and occupied path
from a represented table and a short covering list. No loop run is a premise. -/
theorem scan_model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters)
    (bits start : Nat) (small : bits<64) (startInside : start<2^bits)
    (capacity : p.capacity=BitVec.ofNat 64 (2^bits)) (table : Find.Model32 (BitVec 64))
    (model : Find.KeyModel32 source p (2^bits) table) (order : List Nat) (room : order.length<2^bits)
    (covered : ∀ i<2^bits,table i≠none→i∈order)
    (locals : Find.Locals source p (Find.pathIndex bits start 0)) (enough : order.length≤source.clock) :
    ∃ stop target,stop≤order.length ∧
      evaluateHOLFiniteState source loop=(none,target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-stop} ∧
      Find.Locals target p (Find.pathIndex bits start stop) ∧
      table (Probe.slot (2^bits) start stop)=none ∧
      (∀ step<Placement.distance (2^bits) start (Probe.slot (2^bits) start stop),
        table (Probe.slot (2^bits) start step)≠none) ∧
      ∀ name,ofString "i"≠name→target.locals.lookup name=source.locals.lookup name := by
  have binary (i : Nat) (inside : i<2^bits) :
      Find.usedByte source p (BitVec.ofNat 64 i)=some 0 ∨
        Find.usedByte source p (BitVec.ofNat 64 i)=some 1 := by
    rw [model.used i inside]
    cases table i <;> simp
  have coveredUsed (i : Nat) (inside : i<2^bits) (one : Find.usedByte source p (BitVec.ofNat 64 i)=some 1) : i∈order := by
    apply covered i inside
    intro empty
    rw [model.used i inside,empty] at one
    simp at one
  obtain ⟨stop,bound,empty,occupied⟩:=Find.first_empty source p (2^bits) start (Nat.two_pow_pos bits) startInside order room binary coveredUsed
  obtain ⟨target,run,frame,finalLocals,others⟩:=scan_prefix source p (Find.pathIndex bits start) 0 stop locals
    (by intro j inside;exact Find.path_advance p bits start j small capacity)
    (by intro j lower upper;exact occupied j (by omega))
    (by simpa only [Nat.zero_add,Find.pathIndex] using empty) (by omega)
  have atStop : table (Probe.slot (2^bits) start stop)=none := by
    rw [model.used (Probe.slot (2^bits) start stop) (Nat.mod_lt _ (Nat.two_pow_pos bits))] at empty
    cases cell : table (Probe.slot (2^bits) start stop) with
    | none=>rfl
    | some pair=>simp [cell] at empty
  refine ⟨stop,target,bound,run,frame,by simpa only [Nat.zero_add] using finalLocals,atStop,?_,others⟩
  rw [distance_slot (2^bits) start stop (Nat.two_pow_pos bits) startInside (by omega)]
  intro step inside missing
  have one:=occupied step inside
  rw [model.used (Probe.slot (2^bits) start step) (Nat.mod_lt _ (Nat.two_pow_pos bits)),missing] at one
  simp at one

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.scan_model
