import InitECandidate.Solver.MutableTable.FindChainBuild

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
attribute [local instance] Classical.propDecidable

def pathIndex (bits start index : Nat) : BitVec 64:=BitVec.ofNat 64 (Probe.slot (2^bits) start index)

theorem path_number (bits start index : Nat) (small : bits<64) :
    (pathIndex bits start index).toNat=Probe.slot (2^bits) start index := by
  have capacitySmall : 2^bits<2^64:=Nat.pow_lt_pow_right (by decide) small
  have inside : Probe.slot (2^bits) start index<2^bits:=Nat.mod_lt _ (Nat.two_pow_pos bits)
  rw [pathIndex,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]

theorem path_advance (p : Parameters) (bits start index : Nat) (small : bits<64)
    (capacity : p.capacity=BitVec.ofNat 64 (2^bits)) :
    pathIndex bits start (index+1)=next p (pathIndex bits start index) := by
  apply BitVec.eq_of_toNat_eq
  rw [path_number bits start (index+1) small]
  unfold next
  rw [capacity,Probe.increment _ bits small (by rw [path_number bits start index small];exact Nat.mod_lt _ (Nat.two_pow_pos bits)),
    path_number bits start index small]
  simp only [Probe.slot,Nat.mod_add_mod,Nat.add_assoc]

/-- A concrete table with binary used bytes, occupied slots covered by an
order list and readable32-byte keys supplies the executable probe chain.
This uses no hash distribution or assumed comparator execution. -/
theorem chain32_of_order (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters)
    (bits start : Nat) (small : bits<64) (startInside : start<2^bits)
    (capacity : p.capacity=BitVec.ofNat 64 (2^bits)) (order : List Nat) (room : order.length<2^bits)
    (keys : Nat→WitnessRadix.ByteKeys.Key)
    (binary : ∀ i<2^bits,usedByte snapshot p (BitVec.ofNat 64 i)=some 0 ∨ usedByte snapshot p (BitVec.ofNat 64 i)=some 1)
    (covered : ∀ i<2^bits,usedByte snapshot p (BitVec.ofNat 64 i)=some 1→i∈order)
    (views : ∀ i<2^bits,usedByte snapshot p (BitVec.ofNat 64 i)=some 1→
      WitnessRadix.MemoryBytes.ByteView snapshot (p.keys+BitVec.ofNat 64 i*p.stride) (keys i))
    (fits : ∀ i<2^bits,(p.keys+BitVec.ofNat 64 i*p.stride).toNat+32<2^64) :
    ∃ length≤order.length,Nonempty (Chain32 snapshot p (pathIndex bits start 0) length) := by
  obtain ⟨length,bound,empty,occupied⟩:=first_empty snapshot p (2^bits) start (Nat.two_pow_pos bits) startInside order room binary covered
  refine ⟨length,bound,?_⟩
  exact chain32_of_prefix snapshot p (pathIndex bits start) (fun j=>keys (Probe.slot (2^bits) start j)) 0 length
    (by intro j inside;exact path_advance p bits start j small capacity)
    (by intro j lower upper;exact occupied j (by omega))
    (by simpa only [Nat.zero_add,pathIndex] using empty)
    (by intro j lower upper;exact views _ (Nat.mod_lt _ (Nat.two_pow_pos bits)) (occupied j (by omega)))
    (by intro j lower upper;exact fits _ (Nat.mod_lt _ (Nat.two_pow_pos bits)))

/-- The original lookup scan and absent return use at most6*occupiedCount
source clocks from the actual physical table invariant. Caller/hash/header
setup, preservation of this invariant by mutations and target pricing remain. -/
theorem scan32_count_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters)
    (bits start : Nat) (small : bits<64) (startInside : start<2^bits)
    (capacity : p.capacity=BitVec.ofNat 64 (2^bits)) (order : List Nat) (room : order.length<2^bits)
    (keys : Nat→WitnessRadix.ByteKeys.Key) (query : WitnessRadix.ByteKeys.Key)
    (locals : Locals source p (pathIndex bits start 0)) (keyLength : p.keyLength=32#64)
    (binary : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 0 ∨ usedByte source p (BitVec.ofNat 64 i)=some 1)
    (covered : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 1→i∈order)
    (views : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 1→
      WitnessRadix.MemoryBytes.ByteView source (p.keys+BitVec.ofNat 64 i*p.stride) (keys i))
    (fits : ∀ i<2^bits,(p.keys+BitVec.ofNat 64 i*p.stride).toNat+32<2^64)
    (queryView : WitnessRadix.MemoryBytes.ByteView source p.key query) (queryFits : p.key.toNat+32<2^64)
    (little : source.be=false)
    (code : source.code.lookup (Flapjack.Basis.Pure.MlString.ofString "memeq")=some (WitnessRadix.Memeq32.formals,WitnessRadix.Memeq32.body,.one))
    (enough : 6*order.length≤source.clock) :
    ∃ paid value,paid≤6*order.length ∧
      (evaluateHOLFiniteState source afterIndex).1=some (.returned (.val (.word value))) ∧
      emptyLocalsHOLFinite (evaluateHOLFiniteState source afterIndex).2=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  obtain ⟨length,bound,⟨chain⟩⟩:=chain32_of_order source p bits start small startInside capacity order room keys binary covered views fits
  obtain ⟨paid,paidBound,result,frame⟩:=tail32_execute source p _ length chain query source locals keyLength rfl rfl rfl queryView queryFits little code (by omega)
  exact ⟨paid,(answer chain query).getD p.capacity,by omega,result,frame⟩

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.path_number
#print axioms InitECandidate.Solver.MutableTable.Find.path_advance
#print axioms InitECandidate.Solver.MutableTable.Find.chain32_of_order
#print axioms InitECandidate.Solver.MutableTable.Find.scan32_count_bound
