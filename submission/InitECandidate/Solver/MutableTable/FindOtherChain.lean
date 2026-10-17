import InitECandidate.Solver.MutableTable.FindOtherStep
import InitECandidate.Solver.MutableTable.FindChain32
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Control

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Physical occupied probes ending at an empty byte. This invariant contains
actual read/ownership facts, never comparator decisions or assumed executions.
Capacity/order invariants must construct the finite chain. -/
inductive OtherChain (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (width : Nat) : BitVec 64 → Nat → Prop where
  | empty (index : BitVec 64) (inside : index.toNat < p.capacity.toNat)
      (loaded : usedByte snapshot p index = some 0) : OtherChain snapshot p width index 0
  | occupied (index : BitVec 64) (byte : UInt8) (length : Nat)
      (inside : index.toNat < p.capacity.toNat) (nonzero : byte ≠ 0)
      (loaded : usedByte snapshot p index = some byte)
      (fits : (p.keys + index * p.stride).toNat + width < 2 ^ 64)
      (mapped : ∀ offset < width, snapshot.memaddrs (panByteAlignHOL (width := 64)
        (WitnessRadix.byteAddress (p.keys + index * p.stride) offset)))
      (tail : OtherChain snapshot p width (next p index) length) : OtherChain snapshot p width index (length + 1)

def otherProbePrice (width : Nat) : Nat := MemeqByteRuntime.price (width) + 2

theorem other_probe_price28 : otherProbePrice 28 = 9 := by decide
theorem other_probe_price60 : otherProbePrice 60 = 13 := by decide

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.other_probe_price28
#print axioms InitECandidate.Solver.MutableTable.Find.other_probe_price60
