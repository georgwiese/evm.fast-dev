import InitECandidate.Solver.Input.CurrentHash.ProgressiveEnvironment
import InitECandidate.Solver.Input.ProgressiveBodyCost

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Actual original progressive caller, with the caller tick and complete
allocation/chunk/fold/output/release cost. All non-timeout failures remain. -/
theorem call_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots out zeros stp accel : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (workspace : ShaPair.Workspace source stp accel)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)))
    (inputArena : AllocatedBytes.Arena p (32*n)) (temporaryArena : AllocatedBytes.Arena roots (832+64*n)) (aligned : roots.toNat%8=0)
    (outputArena : AllocatedBytes.Arena out 32) (tableArena : AllocatedBytes.Arena zeros 2048)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p (BitVec.ofNat 64 n) out))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "merkleize_progressive") arguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤115*n+24147 := by
  obtain ⟨callee,called,pLocal,nLocal,outLocal⟩ := environment source.code.lookup p (BitVec.ofNat 64 n) out (original_code source.code workspace.installed)
  exact ClockCost.call_current_terminating source post destination (ofString "merkleize_progressive") arguments (values p (BitVec.ofNat 64 n) out) body callee .one
    (115*n+24146) args called
    (fun result target actual notTimeout=>(body_summary (callEntryStateHOLFinite source callee) target p roots out zeros stp accel n bounded
      (ShaPair.Workspace.at_callee source callee stp accel workspace) pLocal nLocal outLocal heap table inputArena temporaryArena aligned outputArena tableArena result actual notTimeout).1)
    result run notTimeout

/-- A genuine normal progressive call restores its actual entry heap cursor.
The normal callee return is extracted from that same original caller. -/
theorem ignored_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots out zeros stp accel : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (workspace : ShaPair.Workspace source stp accel)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)))
    (inputArena : AllocatedBytes.Arena p (32*n)) (temporaryArena : AllocatedBytes.Arena roots (832+64*n)) (aligned : roots.toNat%8=0)
    (outputArena : AllocatedBytes.Arena out 32) (tableArena : AllocatedBytes.Arena zeros 2048)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p (BitVec.ofNat 64 n) out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "merkleize_progressive") arguments)=(none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)) := by
  obtain ⟨callee,called,pLocal,nLocal,outLocal⟩ := environment source.code.lookup p (BitVec.ofNat 64 n) out (original_code source.code workspace.installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (ofString "merkleize_progressive") arguments run
  have valuesEq : actualValues=values p (BitVec.ofNat 64 n) out := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq : (actualBody,actualCallee,actualShape)=(body,callee,.one) := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have returnedHeap := (body_summary (callEntryStateHOLFinite source callee) target p roots out zeros stp accel n bounded
    (ShaPair.Workspace.at_callee source callee stp accel workspace) pLocal nLocal outLocal heap table inputArena temporaryArena aligned outputArena tableArena (some (.returned returned)) bodyRun (by simp)).2 returned rfl
  rw [endpoint]
  exact returnedHeap

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.environment
#print axioms InitECandidate.Solver.Input.Progressive.call_cost
#print axioms InitECandidate.Solver.Input.Progressive.ignored_return_heap
