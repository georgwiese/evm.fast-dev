import InitECandidate.Solver.MutableTable.FindTail32

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
attribute [local instance] Classical.propDecidable

/-- Construct the executable chain from concrete used-byte/key views along
an actual next-index sequence. No successful loop execution is a premise. -/
theorem chain32_of_prefix (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters)
    (indices : Nat→BitVec 64) (keys : Nat→WitnessRadix.ByteKeys.Key)
    (start length : Nat)
    (advance : ∀ j<start+length,indices (j+1)=next p (indices j))
    (occupied : ∀ j,start≤j→j<start+length→usedByte snapshot p (indices j)=some 1)
    (empty : usedByte snapshot p (indices (start+length))=some 0)
    (views : ∀ j,start≤j→j<start+length→WitnessRadix.MemoryBytes.ByteView snapshot (p.keys+indices j*p.stride) (keys j))
    (fits : ∀ j,start≤j→j<start+length→(p.keys+indices j*p.stride).toNat+32<2^64) :
    Nonempty (Chain32 snapshot p (indices start) length) := by
  induction length generalizing start with
  | zero=>exact ⟨.empty _ (by simpa using empty)⟩
  | succ length ih=>
    have sum : start+1+length=start+(length+1):=by omega
    obtain ⟨tail⟩:=ih (start+1)
      (by intro j inside;exact advance j (by omega))
      (by intro j lower upper;exact occupied j (by omega) (by omega))
      (by rw [sum];exact empty)
      (by intro j lower upper;exact views j (by omega) (by omega))
      (by intro j lower upper;exact fits j (by omega) (by omega))
    rw [advance start (by omega)] at tail
    exact ⟨.occupied _ (keys start) length (occupied start (Nat.le_refl _) (by omega))
      (views start (Nat.le_refl _) (by omega)) (fits start (Nat.le_refl _) (by omega)) tail⟩

/-- Extract the first empty slot from a count-bounded occupied order list.
The used-array/order and byte-view premises must be maintained by actual
construction, insertion, growth, deletion and rollback. -/
theorem first_empty (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters)
    (capacity start : Nat) (positive : 0<capacity) (startInside : start<capacity) (order : List Nat)
    (room : order.length<capacity)
    (binary : ∀ index<capacity,usedByte snapshot p (BitVec.ofNat 64 index)=some 0 ∨ usedByte snapshot p (BitVec.ofNat 64 index)=some 1)
    (covered : ∀ index<capacity,usedByte snapshot p (BitVec.ofNat 64 index)=some 1→index∈order) :
    ∃ stop≤order.length,
      usedByte snapshot p (BitVec.ofNat 64 (Probe.slot capacity start stop))=some 0 ∧
      ∀ index<stop,usedByte snapshot p (BitVec.ofNat 64 (Probe.slot capacity start index))=some 1 := by
  let used : Nat→Prop:=fun i=>i<capacity ∧ usedByte snapshot p (BitVec.ofNat 64 i)=some 1
  obtain ⟨index,bound,empty⟩:=Probe.empty_within_count capacity start order used positive startInside room
    (by intro i occupied;exact covered i occupied.1 occupied.2)
  have slotInside : ∀ i,Probe.slot capacity start i<capacity:=fun i=>Nat.mod_lt _ positive
  have atIndex : usedByte snapshot p (BitVec.ofNat 64 (Probe.slot capacity start index))=some 0 := by
    rcases binary _ (slotInside index) with zero|one
    · exact zero
    · exact False.elim (empty ⟨slotInside index,one⟩)
  have occurrence : ∃ i,usedByte snapshot p (BitVec.ofNat 64 (Probe.slot capacity start i))=some 0:=⟨index,atIndex⟩
  let stop:=Nat.find occurrence
  have atStop:=Nat.find_spec occurrence
  have earliest : stop≤index:=Nat.find_min' occurrence atIndex
  refine ⟨stop,by omega,atStop,?_⟩
  intro earlier inside
  rcases binary _ (slotInside earlier) with zero|one
  · exact False.elim ((Nat.find_min occurrence inside) zero)
  · exact one

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.chain32_of_prefix

#print axioms InitECandidate.Solver.MutableTable.Find.first_empty
