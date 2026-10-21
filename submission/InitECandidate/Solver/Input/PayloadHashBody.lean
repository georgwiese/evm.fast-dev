import InitECandidate.Solver.Input.PayloadHashEntryState

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def bodyPrice (data : Description) := 1+(1+StaticPrefix.price data)

/-- The actual original outer declarations and allocation expose the real
post-allocation execution, including lexical restoration on every outcome. -/
theorem entry_trace (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (out cursor stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : Entry.Ready data origin source lower upper out cursor stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget cursor)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    1≤source.clock ∧ 1≤source.clock-1 ∧ ∃ inner,
      evaluateHOLFiniteState (Entry.chunksEntry data source cursor) afterChunks=(result,inner) ∧ post=Entry.restoreEntry data source inner cursor := by
  rw [entry_shapes.1] at run
  have read : eval source (fieldExpression 0)=some (.val (.word data.raw)) := data.field_read origin source lower upper budget image layout actual.input actual.workspace.sha.domain actual.payload (0,data.raw) (by simp [Description.cells])
  obtain ⟨rawFinal,rawRun,rawEndpoint⟩ := ScalarScope.declare_trace source post "raw" (fieldExpression 0) data.raw afterRaw result read run
  change evaluateHOLFiniteState (Entry.rawEntry data source) afterRaw=(result,rawFinal) at rawRun
  rw [entry_shapes.2.1] at rawRun
  obtain ⟨markFunded,markFinal,markRun,markEndpoint⟩ := HeapScope.mark_call_trace (Entry.rawEntry data source) rawFinal cursor "mark" afterMark actual.heap
    (HeapScope.mark_original_code source.code actual.workspace.sha.installed) result rawRun notTimeout
  change evaluateHOLFiniteState (Entry.markEntry data source cursor) afterMark=(result,markFinal) at markRun
  rw [entry_shapes.2.2] at markRun
  have args : evalListHOLFinite (Entry.markEntry data source cursor) (h:=fun address=>Classical.propDecidable ((Entry.markEntry data source cursor).memaddrs address))
      [.panop .mul [.const 19#64,.const 32#64]]=some (PersistentAlloc.values 608#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,panOpHOL,PersistentAlloc.values,valueIsWord,valueWord]
  have room : cursor.toNat+(608#64).toNat≤33806089496 := by have h:=geometry.arena.upper; change cursor.toNat+608≤33806089496; omega
  obtain ⟨allocFunded,inner,remaining,endpoint⟩ := PersistentAlloc.call_trace (Entry.markEntry data source cursor) markFinal "ch" [.panop .mul [.const 19#64,.const 32#64]] afterChunks cursor 608#64
    args (PersistentAlloc.original_code source.code actual.workspace.sha.installed) actual.heap room result markRun notTimeout
  refine ⟨markFunded,allocFunded,inner,remaining,?_⟩
  rw [rawEndpoint,markEndpoint,endpoint]
  rfl

/-- Complete unchanged htr_payload source-clock bound. Actual transaction
bytes/count, withdrawal count and extra/balance lengths drive the allowance;
all reached non-timeout failure prefixes remain covered. -/
theorem body_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (out cursor stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : Entry.Ready data origin source lower upper out cursor stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget cursor) (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤cursor.toNat)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤bodyPrice data := by
  obtain ⟨markFunded,allocFunded,inner,remaining,endpoint⟩ := entry_trace data origin source post lower upper budget out cursor stp accel chunk zeros image layout actual geometry result run notTimeout
  have next := Entry.chunks_state data origin source lower upper budget out cursor stp accel chunk zeros actual geometry
  have checked := StaticPrefix.after_chunks_cost data origin _ inner lower upper budget cursor out cursor stp accel chunk zeros image layout next geometry separation small before result remaining notTimeout
  have monotone := evaluateHOLFiniteState_clock_le (Entry.chunksEntry data source cursor) afterChunks
  rw [remaining] at monotone
  change inner.clock≤source.clock-1-1 at monotone
  rw [endpoint]
  exact ClockCost.funded_tick source.clock inner.clock (1+StaticPrefix.price data) markFunded
    (Nat.le_trans monotone (Nat.sub_le _ _)) (ClockCost.funded_tick (source.clock-1) inner.clock (StaticPrefix.price data) allocFunded monotone checked)

/-- A genuine normal return of the original whole payload hash restores
its actual entry heap and preserves the full copied/decoded input region. -/
theorem body_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (out cursor stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : Entry.Ready data origin source lower upper out cursor stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget cursor) (outputGeometry : FinalPhase.OutputGeometry out upper)
    (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤cursor.toNat)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) ∧ HashInput.Frame origin post lower upper := by
  obtain ⟨markFunded,allocFunded,inner,remaining,endpoint⟩ := entry_trace data origin source post lower upper budget out cursor stp accel chunk zeros image layout actual geometry (some (.returned value)) run (by simp)
  have next := Entry.chunks_state data origin source lower upper budget out cursor stp accel chunk zeros actual geometry
  have checked := StaticPrefix.after_chunks_normal data origin _ inner lower upper budget cursor out cursor stp accel chunk zeros image layout next geometry outputGeometry separation small before value remaining
  rw [endpoint]
  exact ⟨checked.1,⟨checked.2.words⟩⟩

end InitECandidate.Solver.Input.PayloadHash
#print axioms InitECandidate.Solver.Input.PayloadHash.entry_trace
#print axioms InitECandidate.Solver.Input.PayloadHash.body_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.body_normal
