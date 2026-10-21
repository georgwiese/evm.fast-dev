import InitECandidate.Solver.Input.PayloadHashGeometry
import InitECandidate.Solver.Input.PayloadHashStateCall

namespace InitECandidate.Solver.Input.PayloadHash.Extra
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def call : ProgHOL 64 := .call (some (none,none)) (ofString "htr_bytes_list") StaticFields.extraArguments
def price (data : Description) := data.extraLength/8+115*PackBytes.chunks data.extraLength+149

theorem arguments_read (data : Description) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out cursor mark stp accel chunk zeros : BitVec 64)
    (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out cursor mark stp accel chunk zeros) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) StaticFields.extraArguments=
      some (BytesListHash.values data.extra data.extraLength (ch+320#64)) := by
  have pRead : eval source (fieldExpression 16)=some (.val (.word data.extra)) := data.field_read origin source lower upper budget image layout actual.input actual.ready.workspace.sha.domain actual.payload (16,data.extra) (by simp [Description.cells])
  have nRead : eval source (fieldExpression 24)=some (.val (.word (BitVec.ofNat 64 data.extraLength))) := data.field_read origin source lower upper budget image layout actual.input actual.ready.workspace.sha.domain actual.payload (24,BitVec.ofNat 64 data.extraLength) (by simp [Description.cells])
  have outRead : eval source (StaticFields.outputExpression 10)=some (.val (.word (ch+320#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,StaticFields.outputExpression,FixedHash.offsetExpression,localVar,actual.ready.chunks,valueIsWord,valueWord,wordOpHOL,wordOp]
  simp only [eval] at pRead nRead outRead
  simp only [evalListHOLFinite,StaticFields.extraArguments,evalListHOLExact,pRead,nRead,outRead,BytesListHash.values]
  rfl

theorem current_geometry (data : Description) (lower upper budget : Nat) (raw ch cursor : BitVec 64)
    (layout : data.Layout lower upper budget) (geometry : StaticFields.Geometry raw ch cursor) :
    AllocatedBytes.Arena cursor (832+96*PackBytes.chunks data.extraLength) ∧ AllocatedBytes.Arena (ch+320#64) 32 := by
  have chunksBound := BytesListHash.extra_chunks data.extraLength layout.extraShort
  exact ⟨AllocatedBytes.Arena.weaken cursor 1600 _ geometry.temporaryArena (by omega),
    AllocatedBytes.Arena.subrange ch 608 320 32 geometry.chunksArena (by decide)⟩

/-- Actual original extra-data call, reading current decoded pointer/length
cells after preceding field hashes. All non-timeout failures are included. -/
theorem call_cost (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out cursor mark stp accel chunk zeros : BitVec 64)
    (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out cursor mark stp accel chunk zeros)
    (geometry : StaticFields.Geometry data.raw ch cursor)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source call=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤price data := by
  obtain ⟨temporary,outArena⟩ := current_geometry data lower upper budget data.raw ch cursor layout geometry
  exact BytesListHash.call_cost source post data.extra cursor (ch+320#64) stp accel chunk zeros data.extraLength layout.extraShort actual.ready.workspace actual.ready.heap
    layout.extraArena temporary geometry.aligned outArena (some none) StaticFields.extraArguments (arguments_read data origin source lower upper budget ch out cursor mark stp accel chunk zeros image layout actual) result run notTimeout

/-- Actual normal extra-data hashing restores its entry heap, reinstalls
caller bindings and preserves the whole original decoded/input region. -/
theorem call_normal (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out cursor mark stp accel chunk zeros : BitVec 64)
    (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out cursor mark stp accel chunk zeros)
    (geometry : StaticFields.Geometry data.raw ch cursor) (separation : HashInput.Separation stp accel chunk lower)
    (small : lower<2^64) (before : upper≤ch.toNat)
    (run : evaluateHOLFiniteState source call=(none,post)) : StaticFields.State origin post lower upper data.payload data.raw ch out cursor mark stp accel chunk zeros := by
  obtain ⟨temporary,outArena⟩ := current_geometry data lower upper budget data.raw ch cursor layout geometry
  have args := arguments_read data origin source lower upper budget ch out cursor mark stp accel chunk zeros image layout actual
  have heap := BytesListHash.ignored_return_heap source post data.extra cursor (ch+320#64) stp accel chunk zeros data.extraLength layout.extraShort actual.ready.workspace actual.ready.heap temporary geometry.aligned StaticFields.extraArguments args run
  apply actual.after_call origin source post lower upper data.payload data.raw ch out cursor mark stp accel chunk zeros (ofString "htr_bytes_list") StaticFields.extraArguments run heap
  · intro key different
    exact GlobalEffects.call_body key source.code (some none) (ofString "htr_bytes_list") StaticFields.extraArguments BytesListHash.formals BytesListHash.body .one
      (BytesListHash.original_code source.code actual.ready.workspace.sha.installed) (BytesListHash.globals key source.code actual.ready.workspace.sha.installed different)
  · intro query low high
    have protection := separation.at_word source stp accel chunk zeros query lower actual.ready.workspace small low
    have below : query.toNat<ch.toNat := by omega
    have rootsAway := CopyGeneral.Away.after ch query 608 geometry.chunksAligned (by have h:=geometry.chunksArena.upper; omega) below
    exact BytesListHash.call_memory source post data.extra cursor (ch+320#64) stp accel chunk zeros query data.extraLength layout.extraShort protection actual.ready.heap layout.extraArena temporary geometry.aligned outArena
      (by have h:=geometry.chunksBefore; omega) (CopyGeneral.Away.subrange ch query 608 320 32 rootsAway (by decide)) StaticFields.extraArguments args run

end InitECandidate.Solver.Input.PayloadHash.Extra

#print axioms InitECandidate.Solver.Input.PayloadHash.Extra.arguments_read
#print axioms InitECandidate.Solver.Input.PayloadHash.Extra.current_geometry
#print axioms InitECandidate.Solver.Input.PayloadHash.Extra.call_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.Extra.call_normal
