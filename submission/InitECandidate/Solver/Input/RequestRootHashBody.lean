import InitECandidate.Solver.Input.RequestRootHashEntryState

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.RequestRootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def bodyPrice (data : Description) := 1+(1+pipelinePrice data phases)

theorem entry_trace (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (out ch stp accel chunk zeros : BitVec 64) (actual : Entry.Ready data origin source lower upper out ch stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    1≤source.clock ∧ 1≤source.clock-1 ∧ ∃ inner,evaluateHOLFiniteState (Entry.allocated source ch) (pipeline phases)=(result,inner) ∧ post=Entry.restored source inner ch := by
  rw [body_shape] at run
  obtain ⟨markFunded,markedFinal,markedRun,markedEndpoint⟩ := HeapScope.mark_call_trace source post ch "mark" afterMark actual.heap
    (HeapScope.mark_original_code source.code actual.workspace.sha.installed) result run notTimeout
  change evaluateHOLFiniteState (Entry.marked source ch) afterMark=(result,markedFinal) at markedRun
  change evaluateHOLFiniteState (Entry.marked source ch) (.decCall (ofString "ch") .one (ofString "alloc") [.panop .mul [.const 4#64,.const 32#64]] (pipeline phases))=(result,markedFinal) at markedRun
  have args : evalListHOLFinite (Entry.marked source ch) (h:=fun address=>Classical.propDecidable ((Entry.marked source ch).memaddrs address))
      [.panop .mul [.const 4#64,.const 32#64]]=some (PersistentAlloc.values 128#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,panOpHOL,PersistentAlloc.values,valueIsWord,valueWord]
  have room : ch.toNat+(128#64).toNat≤33806089496 := by have h:=geometry.arena.upper; change ch.toNat+128≤33806089496; omega
  obtain ⟨allocFunded,inner,remaining,endpoint⟩ := PersistentAlloc.call_trace (Entry.marked source ch) markedFinal "ch" [.panop .mul [.const 4#64,.const 32#64]] (pipeline phases) ch 128#64
    args (PersistentAlloc.original_code source.code actual.workspace.sha.installed) actual.heap room result markedRun notTimeout
  refine ⟨markFunded,allocFunded,inner,remaining,?_⟩
  rw [markedEndpoint,endpoint]
  rfl

/-- Whole unchanged htr_new_payload_request203 at actual decoded metadata,
including payload195, blob list, parent copy, requests202, Merkle4 and outer
mark/allocation/release. This remains a source call/loop clock allowance. -/
theorem body_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (out ch stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : Entry.Ready data origin source lower upper out ch stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : PayloadHash.FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤bodyPrice data := by
  obtain ⟨markFunded,allocFunded,inner,remaining,endpoint⟩ := entry_trace data origin source post lower upper budget out ch stp accel chunk zeros actual geometry result run notTimeout
  have ready := Entry.allocated_ready data origin source lower upper budget out ch stp accel chunk zeros actual geometry
  have checked := pipeline_cost phases data origin _ inner lower upper budget ch out ch stp accel chunk zeros image layout ready geometry outputGeometry separation small before result remaining notTimeout
  have monotone := evaluateHOLFiniteState_clock_le (Entry.allocated source ch) (pipeline phases)
  rw [remaining] at monotone
  change inner.clock≤source.clock-1-1 at monotone
  rw [endpoint]
  exact ClockCost.funded_tick source.clock inner.clock (1+pipelinePrice data phases) markFunded
    (Nat.le_trans monotone (Nat.sub_le _ _)) (ClockCost.funded_tick (source.clock-1) inner.clock (pipelinePrice data phases) allocFunded monotone checked)

theorem body_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (out ch stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : Entry.Ready data origin source lower upper out ch stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (outputGeometry : PayloadHash.FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)) ∧ HashInput.Frame origin post lower upper := by
  obtain ⟨markFunded,allocFunded,inner,remaining,endpoint⟩ := entry_trace data origin source post lower upper budget out ch stp accel chunk zeros actual geometry (some (.returned value)) run (by simp)
  have ready := Entry.allocated_ready data origin source lower upper budget out ch stp accel chunk zeros actual geometry
  have checked := pipeline_normal phases data origin _ inner lower upper budget ch out ch stp accel chunk zeros image layout ready geometry outputGeometry separation small before value remaining
  rw [endpoint]
  exact ⟨checked.1,⟨checked.2.words⟩⟩

end InitECandidate.Solver.Input.RequestRootHash
#print axioms InitECandidate.Solver.Input.RequestRootHash.entry_trace
#print axioms InitECandidate.Solver.Input.RequestRootHash.body_cost
#print axioms InitECandidate.Solver.Input.RequestRootHash.body_normal
