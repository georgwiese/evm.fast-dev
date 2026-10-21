import InitECandidate.Solver.Input.PayloadHashGeometry
import InitECandidate.Solver.Input.PayloadHashStateCall

namespace InitECandidate.Solver.Input.PayloadHash.BalancePhase
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def call : ProgHOL 64 := .call (some (none,none)) (ofString "htr_pbytes") StaticFields.balanceArguments
def price (data : Description) := data.balanceLength/8+115*PackBytes.chunks data.balanceLength+24283

theorem arguments_read (data : Description) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) StaticFields.balanceArguments=some (PBytes.values data.balance data.balanceLength (ch+544#64)) := by
  have pRead : eval source (fieldExpression 64)=some (.val (.word data.balance)) := data.field_read origin source lower upper budget image layout actual.input actual.ready.workspace.sha.domain actual.payload (64,data.balance) (by simp [Description.cells])
  have nRead : eval source (fieldExpression 72)=some (.val (.word (BitVec.ofNat 64 data.balanceLength))) := data.field_read origin source lower upper budget image layout actual.input actual.ready.workspace.sha.domain actual.payload (72,BitVec.ofNat 64 data.balanceLength) (by simp [Description.cells])
  have outRead : eval source (StaticFields.outputExpression 17)=some (.val (.word (ch+544#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,StaticFields.outputExpression,FixedHash.offsetExpression,localVar,actual.ready.chunks,valueIsWord,valueWord,wordOpHOL,wordOp]
  simp only [eval] at pRead nRead outRead
  simp only [evalListHOLFinite,StaticFields.balanceArguments,evalListHOLExact,pRead,nRead,outRead,PBytes.values]

theorem current_geometry (data : Description) (lower upper budget : Nat) (ch : BitVec 64)
    (layout : data.Layout lower upper budget) (geometry : data.RuntimeGeometry budget ch) :
    AllocatedBytes.Arena (chunksCursor ch) (832+96*PackBytes.chunks data.balanceLength) ∧ AllocatedBytes.Arena (ch+544#64) 32 := by
  obtain ⟨fixed,scratch,number⟩ := data.static_geometry lower upper budget ch layout geometry
  have chunksBound : PackBytes.chunks data.balanceLength≤PackBytes.chunks budget := by have h:=layout.balanceBound; unfold PackBytes.chunks; omega
  exact ⟨AllocatedBytes.Arena.weaken _ (data.scratchBytes budget) _ scratch (by unfold Description.scratchBytes; omega),
    AllocatedBytes.Arena.subrange ch 608 544 32 fixed.chunksArena (by decide)⟩

theorem call_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source call=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤price data := by
  obtain ⟨temporary,outArena⟩ := current_geometry data lower upper budget ch layout geometry
  have fixed := (data.static_geometry lower upper budget ch layout geometry).1
  exact PBytes.call_cost source post data.balance (chunksCursor ch) (ch+544#64) stp accel chunk zeros data.balanceLength (by have a:=layout.balanceBound; have b:=layout.budgetBound; omega)
    actual.ready.workspace actual.ready.heap layout.balanceArena temporary fixed.aligned outArena (some none) StaticFields.balanceArguments
    (arguments_read data origin source lower upper budget ch out mark stp accel chunk zeros image layout actual) result run notTimeout

/-- The actual balance hash preserves decoded/input memory and restores the
released shared cursor, independent of balance bytes or digest values. -/
theorem call_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (run : evaluateHOLFiniteState source call=(none,post)) : StaticFields.State origin post lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros := by
  obtain ⟨temporary,outArena⟩ := current_geometry data lower upper budget ch layout geometry
  have fixed := (data.static_geometry lower upper budget ch layout geometry).1
  have args := arguments_read data origin source lower upper budget ch out mark stp accel chunk zeros image layout actual
  have bounded : data.balanceLength≤134217728 := by have a:=layout.balanceBound; have b:=layout.budgetBound; omega
  have heap := PBytes.ignored_return_heap source post data.balance (chunksCursor ch) (ch+544#64) stp accel chunk zeros data.balanceLength bounded actual.ready.workspace actual.ready.heap temporary fixed.aligned outArena StaticFields.balanceArguments args run
  apply actual.after_call origin source post lower upper data.payload data.raw ch out (chunksCursor ch) mark stp accel chunk zeros (ofString "htr_pbytes") StaticFields.balanceArguments run heap
  · intro key different
    exact GlobalEffects.call_body key source.code (some none) (ofString "htr_pbytes") StaticFields.balanceArguments PBytes.formals PBytes.body .one
      (PBytes.original_code source.code actual.ready.workspace.sha.installed) (PBytes.globals key source.code actual.ready.workspace.sha.installed different)
  · intro query low high
    have protection := separation.at_word source stp accel chunk zeros query lower actual.ready.workspace small low
    have below : query.toNat<ch.toNat := by omega
    have rootsAway := CopyGeneral.Away.after ch query 608 fixed.chunksAligned (by have h:=fixed.chunksArena.upper; omega) below
    exact PBytes.call_memory source post data.balance (chunksCursor ch) (ch+544#64) stp accel chunk zeros query data.balanceLength bounded protection actual.ready.heap layout.balanceArena temporary fixed.aligned outArena
      (by have h:=fixed.chunksBefore; omega) (CopyGeneral.Away.subrange ch query 608 544 32 rootsAway (by decide)) StaticFields.balanceArguments args run

end InitECandidate.Solver.Input.PayloadHash.BalancePhase

#print axioms InitECandidate.Solver.Input.PayloadHash.BalancePhase.arguments_read
#print axioms InitECandidate.Solver.Input.PayloadHash.BalancePhase.current_geometry
#print axioms InitECandidate.Solver.Input.PayloadHash.BalancePhase.call_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.BalancePhase.call_normal
