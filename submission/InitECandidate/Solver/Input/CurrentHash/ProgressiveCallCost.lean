import InitECandidate.Solver.Input.CurrentHash.ProgressiveBodyCost
import InitECandidate.Solver.Input.CurrentHash.ProgressiveEnvironment
import InitECandidate.Solver.Input.ClockCostTerminatingCall

namespace InitECandidate.Solver.Input.CurrentHash.ProgressiveCallCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real three-word software progressive-hash caller, priced from the same
non-timeout invocation. Missing mapping, failed allocations and trapped hashes
are included; no successful return or obsolete SHA workspace is assumed. -/
theorem cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64) (n : Nat)
    (bounded : n ≤ 134217728) (installed : OriginalCode.Installed source.code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some (Progressive.values p (BitVec.ofNat 64 n) out))
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "merkleize_progressive") arguments) = (result, post))
    (notTimeout : result ≠ some .timeOut) : source.clock - post.clock ≤ 88*n + 3121 := by
  obtain ⟨callee, called, pointer, count, output⟩ := Progressive.environment source.code.lookup p (BitVec.ofNat 64 n) out (Progressive.original_code source.code installed)
  exact ClockCost.call_current_terminating source post destination (ofString "merkleize_progressive") arguments (Progressive.values p (BitVec.ofNat 64 n) out)
    Progressive.body callee .one (88*n+3120) args called
    (fun result target evaluated notTimeout => ProgressiveBodyCost.cost (callEntryStateHOLFinite source callee) target p n bounded installed pointer count result evaluated notTimeout)
    result actual notTimeout

end InitECandidate.Solver.Input.CurrentHash.ProgressiveCallCost

#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveCallCost.cost
