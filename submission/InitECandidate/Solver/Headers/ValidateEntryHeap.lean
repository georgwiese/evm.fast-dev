import InitECandidate.Solver.Headers.ValidateEntry

namespace InitECandidate.Solver.Headers.Validate
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Exact original array-allocation frontier. Both sizes and the incoming
heap are multiples of eight, so neither allocation introduces padding. -/
theorem entryHeap_number (heap count : BitVec 64) (small : count.toNat≤256)
    (aligned : heap.toNat%8=0)
    (firstRoom : heap.toNat+(hsSize count).toNat≤33806089496)
    (secondRoom : (hashesPointer heap count).toNat+(hashesSize count).toNat≤33806089496) :
    (entryHeap heap count).toNat=heap.toNat+40*count.toNat+40 := by
  have sizes:=size_numbers count small
  have firstNumber : (hashesPointer heap count).toNat=heap.toNat+8*count.toNat+8 := by
    rw [hashesPointer,PersistentAlloc.rounded_nat heap (hsSize count) (by omega),sizes.1]
    omega
  have firstAligned : (hashesPointer heap count).toNat%8=0 := (PersistentAlloc.guards heap (hsSize count) firstRoom).2.2.2.2
  rw [entryHeap,PersistentAlloc.rounded_nat (hashesPointer heap count) (hashesSize count) (by omega),sizes.2]
  omega

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.entryHeap_number
