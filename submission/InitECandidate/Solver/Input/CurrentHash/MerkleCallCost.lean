import InitECandidate.Solver.Input.CurrentHash.MerkleBodyCost
import InitECandidate.Solver.Input.MerkleEnvironment
import InitECandidate.Solver.Input.ClockCostTerminatingCall

namespace InitECandidate.Solver.Input.CurrentHash.MerkleCallCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual four-word software Merkle caller inherits the complete body
bound, including errors, traps and FFI outcomes. Non-timeout is supplied by the
same enclosing observation, and does not assume a successful Merkle return. -/
theorem cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p n limit out : BitVec 64) (budget : Nat)
    (small : budget < 58) (countBound : n.toNat ≤ 2^budget) (limitBound : limit.toNat ≤ 2^budget)
    (installed : OriginalCode.Installed source.code) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (Merkle.values p n limit out))
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "merkleize") arguments) = (result, post))
    (notTimeout : result ≠ some .timeOut) : source.clock - post.clock ≤ 88*n.toNat + 4*budget + 49 := by
  obtain ⟨callee, called, pointer, count, maximum, output⟩ := Merkle.environment source.code.lookup p n limit out (Merkle.original_code source.code installed)
  have bodyCost : ∀ result target, evaluateHOLFiniteState (callEntryStateHOLFinite source callee) Merkle.body = (result, target) → result ≠ some .timeOut →
      (callEntryStateHOLFinite source callee).clock - target.clock ≤ 88*n.toNat + 4*budget + 48 := by
    intro result target evaluated notTimeout
    rw [← MerkleBodyCost.source_shape.1] at evaluated
    exact MerkleBodyCost.cost (callEntryStateHOLFinite source callee) target p n limit budget small countBound limitBound
      installed pointer count maximum result evaluated notTimeout
  exact ClockCost.call_current_terminating source post destination (ofString "merkleize") arguments (Merkle.values p n limit out)
    Merkle.body callee .one (88*n.toNat + 4*budget + 48) args called bodyCost result actual notTimeout

end InitECandidate.Solver.Input.CurrentHash.MerkleCallCost

#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleCallCost.cost
