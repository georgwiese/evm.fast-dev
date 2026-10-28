import InitECandidate.Solver.Input.CurrentHash.PackBytesReturn
import InitECandidate.Solver.Input.PackBytesEnvironment
import InitECandidate.Solver.Input.ClockCostCallReached
import InitECandidate.Solver.Input.ClockCostTerminatingScoped

namespace InitECandidate.Solver.Input.CurrentHash.PackBytesCallCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : BitVec 64) (n : Nat)
    (installed : OriginalCode.Installed source.code) (small : n + 64 < 2^64)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (PackBytes.values p n)) :
    source.clock - (evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "pack_bytes") arguments)).2.clock ≤ PackBytesCost.price n + 1 := by
  obtain ⟨callee, called, pointer, length⟩ := PackBytes.environment source.code.lookup p n (PackBytes.original_code source.code installed)
  exact ClockCost.call_current source destination (ofString "pack_bytes") arguments (PackBytes.values p n) PackBytes.body callee PackBytes.returnShape
    (PackBytesCost.price n) args called (PackBytesCost.cost (callEntryStateHOLFinite source callee) p n installed small pointer length)

/-- Price an actual scoped pack call and a suffix using its real returned tuple.
Only a genuine checked return supplies the buffer and ceil(n/32) count; failed
pack executions never invoke the continuation contract. -/
theorem scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : BitVec 64) (n : Nat)
    (installed : OriginalCode.Installed source.code) (small : n + 64 < 2^64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (PackBytes.values p n))
    (tail : ∀ post : PanSemStateFiniteExact 64 Guest.HostMemory, ∀ buffer : BitVec 64, post.code = source.code →
      post.clock - (evaluateHOLFiniteState (CallNormal.continuationEntry source post name (PackBytesReturn.tuple buffer n)) continuation).2.clock ≤ tailPrice) :
    source.clock - (evaluateHOLFiniteState source (.decCall (ofString name) PackBytes.returnShape (ofString "pack_bytes") arguments continuation)).2.clock ≤
      PackBytesCost.price n + tailPrice + 1 := by
  obtain ⟨callee, called, pointer, length⟩ := PackBytes.environment source.code.lookup p n (PackBytes.original_code source.code installed)
  apply ClockCost.scoped_reached_current source name PackBytes.returnShape (ofString "pack_bytes") arguments (PackBytes.values p n)
    PackBytes.body continuation callee PackBytes.returnShape (PackBytesCost.price n) tailPrice args called
    (PackBytesCost.cost (callEntryStateHOLFinite source callee) p n installed small pointer length)
  intro post value returned checked
  obtain ⟨buffer, rfl⟩ := PackBytesReturn.body_return (callEntryStateHOLFinite source callee) post p n (by omega) pointer length value returned
  exact tail post buffer ((evaluation_fields (callEntryStateHOLFinite source callee) post PackBytes.body _ returned).2.2.2)

/-- The corresponding same-observation composition when a later Merkle call
is priced for non-timeout outcomes. Each normal packed tuple is still derived
from this exact invocation, without assuming packing or hashing succeeds. -/
theorem scoped_cost_terminating (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p : BitVec 64) (n : Nat)
    (installed : OriginalCode.Installed source.code) (small : n + 64 < 2^64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (PackBytes.values p n))
    (tail : ∀ target : PanSemStateFiniteExact 64 Guest.HostMemory, ∀ buffer : BitVec 64, target.code = source.code →
      ∀ result final, evaluateHOLFiniteState (CallNormal.continuationEntry source target name (PackBytesReturn.tuple buffer n)) continuation = (result, final) →
        result ≠ some .timeOut → target.clock - final.clock ≤ tailPrice)
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (.decCall (ofString name) PackBytes.returnShape (ofString "pack_bytes") arguments continuation) = (result, post))
    (notTimeout : result ≠ some .timeOut) : source.clock - post.clock ≤ PackBytesCost.price n + tailPrice + 1 := by
  obtain ⟨callee, called, pointer, length⟩ := PackBytes.environment source.code.lookup p n (PackBytes.original_code source.code installed)
  apply ClockCost.scoped_reached_terminating source post name PackBytes.returnShape (ofString "pack_bytes") arguments (PackBytes.values p n)
    PackBytes.body continuation callee PackBytes.returnShape (PackBytesCost.price n) tailPrice args called
    (by intro result target evaluated notTimeout
        have price := PackBytesCost.cost (callEntryStateHOLFinite source callee) p n installed small pointer length
        rw [evaluated] at price
        exact price) ?_ result actual notTimeout
  intro target value returned checked
  obtain ⟨buffer, rfl⟩ := PackBytesReturn.body_return (callEntryStateHOLFinite source callee) target p n (by omega) pointer length value returned
  exact tail target buffer ((evaluation_fields (callEntryStateHOLFinite source callee) target PackBytes.body _ returned).2.2.2)

end InitECandidate.Solver.Input.CurrentHash.PackBytesCallCost

#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesCallCost.cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesCallCost.scoped_cost

#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesCallCost.scoped_cost_terminating
