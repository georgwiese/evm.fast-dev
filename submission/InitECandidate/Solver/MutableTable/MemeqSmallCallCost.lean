import InitECandidate.Solver.MutableTable.MemeqSmallNormal
import InitECandidate.Solver.Input.ClockCostCurrentScoped

namespace InitECandidate.Solver.MutableTable.MemeqSmall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Current mapped operands price the actual original comparison at every
outcome. A clock-free literal continuation adds no source call/loop ticks. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64) (length : Nat)
    (small : length ≤ 64) (aFits : a.toNat + length < 2^64) (bFits : b.toNat + length < 2^64)
    (leftMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress a offset)))
    (rightMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress b offset)))
    (code : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some (MemeqByteRuntime.values a b length))
    (quiet : Input.ClockCost.Bound source.code continuation 0) :
    source.clock - (evaluateHOLFiniteState source (.decCall name .one (ofString "memeq") arguments continuation)).2.clock ≤
      MemeqByteRuntime.price length + 1 := by
  obtain ⟨callee, called, aLocal, bLocal, lengthLocal⟩ := MemeqByteRuntime.environment source.code.lookup a b length code
  let entry := callEntryStateHOLFinite source callee
  have cost := body_cost entry a b length aLocal bLocal lengthLocal small aFits bFits leftMapped rightMapped
  exact Input.ClockCost.scoped_current source name .one (ofString "memeq") arguments _ Memeq32.body continuation callee .one
    (MemeqByteRuntime.price length) 0 args called cost quiet

end InitECandidate.Solver.MutableTable.MemeqSmall

#print axioms InitECandidate.Solver.MutableTable.MemeqSmall.call_cost
