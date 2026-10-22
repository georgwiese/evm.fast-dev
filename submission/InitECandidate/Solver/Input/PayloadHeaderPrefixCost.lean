import InitECandidate.Solver.Input.PayloadHeaderProgram
import InitECandidate.Solver.WitnessRadix.KeccakAnyDynamic
import InitECandidate.Solver.WitnessRadix.AllocationCost

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

private theorem widen {code} {program : ProgHOL 64} {small large : Nat}
    (priced : ClockCost.Bound code program small) (bound : small≤large) : ClockCost.Bound code program large :=
  ClockCost.mono code program small large priced bound

theorem zero_fixed (code) (installed : OriginalCode.Installed code) (dst : ExpHOL 64) (length : Nat)
    (small : length+32<2^64) :
    ClockCost.Bound code (.call (some (none,none)) (ofString "memzero") [dst,.const (BitVec.ofNat 64 length)]) (ZeroAny.price length+1) := by
  intro source codeEq
  exact BufferDynamicCost.zero_cost source dst (.const (BitVec.ofNat 64 length)) length (by rw [codeEq]; exact installed) small rfl

theorem hash_fixed (code) (installed : OriginalCode.Installed code) (pointer out : ExpHOL 64) (length : Nat)
    (small : length+136<2^64) :
    ClockCost.Bound code (.call (some (none,none)) (ofString "keccak256") [pointer,.const (BitVec.ofNat 64 length),out])
      (Keccak256.AnyCost.bodyPrice length+1) := by
  intro source codeEq
  exact Keccak256.AnyCost.dynamic_call_cost source pointer (.const (BitVec.ofNat 64 length)) out length
    (by rw [codeEq]; exact installed) small rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All original payload_header work before block_rlp_length has a fixed
source allowance, including every allocator/hash/copy/store failure. The
arbitrary real remaining code is charged separately at its own allowance. -/
theorem prefix_cost (code) (installed : OriginalCode.Installed code) (tail : ProgHOL 64) (tailPrice : Nat)
    (priced : ClockCost.Bound code tail tailPrice) :
    ClockCost.Bound code (CallPrefix.program actions tail) (tailPrice+1011) := by
  apply widen
  · simp only [actions,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
      Option.map_some,Option.map_none,CallPrefix.cut,
      show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,CallPrefix.program]
    repeat' first
      | exact priced
      | apply ClockCost.declared
      | apply PersistentAlloc.scoped_price code installed
      | apply ClockCost.sequence
      | exact ClockCost.store code _ _
      | exact ClockCost.of_quiet code _ (QuietClock.store_byte code _ _)
      | exact zero_fixed code installed _ _ (by decide)
      | exact hash_fixed code installed _ _ _ (by decide)
  · unfold ZeroAny.price Keccak256.AnyCost.bodyPrice
    omega

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.prefix_cost
