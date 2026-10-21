import InitECandidate.Solver.Input.FixedHashAllocation
import InitECandidate.Solver.Input.HeapMarkTrace

namespace InitECandidate.Solver.Input.FixedHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def Kind.price (kind : Kind) := (kind.steps.map Step.price).sum+kind.tailPrice+2

/-- The complete original fixed field pipeline, including its actual
allocation and real normal-return restoration of the saved outer mark. -/
theorem after_mark_summary (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p ch out mark stp accel chunk zeros : BitVec 64)
    (workspace : SszHash.Workspace source stp accel chunk zeros)
    (pointer : source.locals.lookup (ofString kind.inputName)=some (.val (.word p)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (inputArena : AllocatedBytes.Arena p kind.length) (arena : AllocatedBytes.Arena ch (32*kind.count+1120)) (aligned : ch.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source kind.afterMark=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤(kind.steps.map Step.price).sum+kind.tailPrice+1 ∧
      (∀ value,result=some (.returned value) → post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark))) := by
  obtain ⟨paid,final,remaining,endpoint⟩ := allocation_trace kind source post ch workspace.sha.installed heap arena result run notTimeout
  obtain ⟨round,geometry⟩ := allocation_geometry kind ch p inputArena arena aligned
  let entry := kind.allocated source ch
  have ready := allocated_ready kind source p ch out mark stp accel chunk zeros workspace pointer output saved round
  have price := pipeline_cost kind.steps kind.inputName kind.afterSteps kind.tailPrice kind.length kind.count p ch out (kind.cursor ch) mark stp accel chunk zeros (steps_valid kind) geometry
    (fun current target currentReady actual evaluated notTimeout=>after_steps_cost kind current target p ch out (kind.cursor ch) mark stp accel chunk zeros currentReady geometry outArena actual evaluated notTimeout)
    entry final ready result remaining notTimeout
  have monotone := evaluateHOLFiniteState_clock_le entry kind.afterAllocation
  rw [remaining] at monotone
  change final.clock≤entry.clock at monotone
  have entryClock : entry.clock=source.clock-1 := rfl
  have endpointClock : post.clock=final.clock := by rw [endpoint]; rfl
  refine ⟨by rw [endpointClock]; omega,?_⟩
  intro value returned
  have actualRun := remaining
  rw [returned] at actualRun
  have restored := pipeline_return_heap kind.steps kind.inputName kind.afterSteps kind.length kind.count p ch out (kind.cursor ch) mark stp accel chunk zeros (steps_valid kind) geometry
    (fun current target currentReady value evaluated=>after_steps_return_heap kind current target p ch out (kind.cursor ch) mark stp accel chunk zeros currentReady geometry value evaluated)
    entry final ready value actualRun
  rw [endpoint]
  exact restored

/-- All six unchanged fixed record hashes: real scalar/vector/copy fields,
actual dense Merkle tree and both original heap scopes. All non-timeout
outcomes have the stated price; normal returns restore their entry heap. -/
theorem body_summary (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p ch out stp accel chunk zeros : BitVec 64)
    (workspace : SszHash.Workspace source stp accel chunk zeros)
    (pointer : source.locals.lookup (ofString kind.inputName)=some (.val (.word p)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (inputArena : AllocatedBytes.Arena p kind.length) (arena : AllocatedBytes.Arena ch (32*kind.count+1120)) (aligned : ch.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source kind.body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤kind.price ∧
      (∀ value,result=some (.returned value) → post.globals.lookup (ofString "heap_ptr")=some (.val (.word ch))) := by
  rw [body_shape] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post ch "mark" kind.afterMark heap
    (HeapScope.mark_original_code source.code workspace.sha.installed) result run notTimeout
  let entry := bind {source with clock:=source.clock-1} "mark" ch
  have nextWorkspace := SszHash.Workspace.of_fields source entry stp accel chunk zeros workspace rfl rfl (by intro key different; rfl)
  have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other _ "mark" name ch different
  have summary := after_mark_summary kind entry final p ch out ch stp accel chunk zeros nextWorkspace
    ((other kind.inputName (by cases kind <;> decide)).trans pointer) ((other "out" (by decide)).trans output) (bind_lookup_same _ _ _)
    heap inputArena arena aligned outArena result remaining notTimeout
  have monotone := evaluateHOLFiniteState_clock_le entry kind.afterMark
  rw [remaining] at monotone
  change final.clock≤entry.clock at monotone
  have entryClock : entry.clock=source.clock-1 := rfl
  have endpointClock : post.clock=final.clock := by rw [endpoint]; rfl
  refine ⟨?_,?_⟩
  · rw [endpointClock]
    have price := summary.1
    unfold Kind.price
    omega
  · intro value returned
    rw [endpoint]
    exact summary.2 value returned

/-- Exact evaluated source-clock prices, retaining small-vector fast paths. -/
theorem fixed_prices : Kind.withdrawal.price=615 ∧ Kind.deposit.price=1710 ∧ Kind.wdreq.price=871 ∧ Kind.cons.price=1247 ∧ Kind.bdep.price=1535 ∧ Kind.bexit.price=696 := by decide

theorem globals (kind : Kind) (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code kind.body := by
  rw [body_shape]
  unfold Kind.afterMark
  apply GlobalEffects.scoped_body key code _ _ (ofString "heap_mark") _ _ _ _ _ (HeapScope.mark_original_code code installed) (Merkle.mark_globals key code)
  apply GlobalEffects.scoped_body key code _ _ (ofString "alloc") _ _ _ _ _ (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed different)
  exact pipeline_globals kind.steps kind.inputName kind.afterSteps key code installed different (after_steps_globals kind key code installed different)

end InitECandidate.Solver.Input.FixedHash

#print axioms InitECandidate.Solver.Input.FixedHash.after_mark_summary
#print axioms InitECandidate.Solver.Input.FixedHash.body_summary
#print axioms InitECandidate.Solver.Input.FixedHash.fixed_prices
#print axioms InitECandidate.Solver.Input.FixedHash.globals
