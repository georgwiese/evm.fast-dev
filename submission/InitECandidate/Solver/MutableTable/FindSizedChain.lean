import InitECandidate.Solver.MutableTable.FindSizedStep
import InitECandidate.Solver.MutableTable.FindChain32
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Control

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Physical occupied probes ending at an empty byte. This invariant contains
actual read/ownership facts, never comparator decisions or assumed executions.
Capacity/order invariants must construct the finite chain. -/
inductive SizedChain (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (kind : HashSized.Kind) : BitVec 64 → Nat → Prop where
  | empty (index : BitVec 64) (inside : index.toNat < p.capacity.toNat)
      (loaded : usedByte snapshot p index = some 0) : SizedChain snapshot p kind index 0
  | occupied (index : BitVec 64) (byte : UInt8) (length : Nat)
      (inside : index.toNat < p.capacity.toNat) (nonzero : byte ≠ 0)
      (loaded : usedByte snapshot p index = some byte)
      (fits : (p.keys + index * p.stride).toNat + HashSized.keySize kind < 2 ^ 64)
      (mapped : ∀ offset < HashSized.keySize kind, snapshot.memaddrs (panByteAlignHOL (width := 64)
        (WitnessRadix.byteAddress (p.keys + index * p.stride) offset)))
      (tail : SizedChain snapshot p kind (next p index) length) : SizedChain snapshot p kind index (length + 1)

def sizedProbePrice (kind : HashSized.Kind) : Nat := MemeqByteRuntime.price (HashSized.keySize kind) + 2

theorem sized_probe_price20 : sizedProbePrice .address = 8 := by decide
theorem sized_probe_price52 : sizedProbePrice .storage = 12 := by decide

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.sized_probe_price20
#print axioms InitECandidate.Solver.MutableTable.Find.sized_probe_price52
