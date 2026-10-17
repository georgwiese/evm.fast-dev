import InitECandidate.Solver.MutableTable.FindGeneralStep
import InitECandidate.Solver.MutableTable.FindChain32
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Control

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Physical occupied probes ending at an empty byte. This invariant contains
actual read/ownership facts, never comparator decisions or assumed executions.
Capacity/order invariants must construct the finite chain. -/
inductive GeneralChain (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (kind : KeyHash.Kind) : BitVec 64 → Nat → Prop where
  | empty (index : BitVec 64) (inside : index.toNat < p.capacity.toNat)
      (loaded : usedByte snapshot p index = some 0) : GeneralChain snapshot p kind index 0
  | occupied (index : BitVec 64) (byte : UInt8) (length : Nat)
      (inside : index.toNat < p.capacity.toNat) (nonzero : byte ≠ 0)
      (loaded : usedByte snapshot p index = some byte)
      (fits : (p.keys + index * p.stride).toNat + KeyHash.keySize kind < 2 ^ 64)
      (mapped : ∀ offset < KeyHash.keySize kind, snapshot.memaddrs (panByteAlignHOL (width := 64)
        (WitnessRadix.byteAddress (p.keys + index * p.stride) offset)))
      (tail : GeneralChain snapshot p kind (next p index) length) : GeneralChain snapshot p kind index (length + 1)

def generalProbePrice (kind : KeyHash.Kind) : Nat := MemeqByteRuntime.price (KeyHash.keySize kind) + 2

theorem general_probe_price (kind : KeyHash.Kind) : generalProbePrice kind = MemeqByteRuntime.price (KeyHash.keySize kind) + 2 := rfl

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.general_probe_price
