import InitECandidate.Solver.Input.MerkleBodyHeap
import InitECandidate.Solver.Input.MerkleCallCost

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- The real normal ignored Merkle call restores the current heap cursor.
The normal callee return and exact ABI are derived from that same call. -/
theorem ignored_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p n limit cursor out stp accel : BitVec 64) (depth : Nat)
    (small : depth<64) (countBound : n.toNat≤2^depth) (limitBound : limit.toNat≤2^depth)
    (workspace : ShaPair.Workspace source stp accel)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p (32*n.toNat))
    (bufferArena : AllocatedBytes.Arena cursor (32*max 1 (2*n.toNat))) (aligned : cursor.toNat%8=0)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p n limit out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "merkleize") arguments)=(none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  obtain ⟨callee,called,pLocal,nLocal,limitLocal,outLocal⟩ := environment source.code.lookup p n limit out (original_code source.code workspace.installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (ofString "merkleize") arguments run
  have valuesEq : actualValues=values p n limit out := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq : (actualBody,actualCallee,actualShape)=(body,callee,.one) := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have returnedHeap := body_return_heap (callEntryStateHOLFinite source callee) target p n limit cursor stp accel depth
    small countBound limitBound (ShaPair.Workspace.at_callee source callee stp accel workspace) pLocal nLocal limitLocal heap inputArena bufferArena aligned returned bodyRun
  rw [endpoint]
  exact returnedHeap

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.ignored_return_heap
