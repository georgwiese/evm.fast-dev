import InitECandidate.Solver.Input.PayloadHashGeometry
import InitECandidate.Solver.Input.PayloadHashStateCall

namespace InitECandidate.Solver.Input.PayloadHash.ListPhase
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

inductive Kind where | transactions | withdrawals

def Kind.count (kind : Kind) (data : Description) := match kind with | .transactions=>data.transactionCount | .withdrawals=>data.withdrawalCount
def Kind.name : Kind→String | .transactions=>"ntx" | .withdrawals=>"nwd"
def Kind.slot : Kind→Nat | .transactions=>13 | .withdrawals=>14
def Kind.cursor (kind : Kind) (data : Description) (ch : BitVec 64) := afterRoots (chunksCursor ch) (kind.count data)
def Kind.arguments (kind : Kind) := listArguments kind.name kind.slot
def Kind.call (kind : Kind) : ProgHOL 64 := .call (some (none,none)) (ofString "htr_plist_chunks") kind.arguments

theorem current_geometry (kind : Kind) (data : Description) (lower upper budget : Nat) (ch : BitVec 64)
    (layout : data.Layout lower upper budget) (geometry : data.RuntimeGeometry budget ch) :
    kind.count data≤134217728 ∧ AllocatedBytes.Arena (chunksCursor ch) (32*kind.count data) ∧
    AllocatedBytes.Arena (kind.cursor data ch) (832+64*kind.count data) ∧ (kind.cursor data ch).toNat%8=0 ∧
    AllocatedBytes.Arena (ch+BitVec.ofNat 64 (32*kind.slot)) 32 := by
  obtain ⟨fixed,scratch,cursorNumber⟩ := data.static_geometry lower upper budget ch layout geometry
  have fits : rootsBytes (kind.count data)+max 0 (832+64*kind.count data)≤data.scratchBytes budget := by
    cases kind <;> simp only [Kind.count] <;> unfold rootsBytes Description.scratchBytes <;> omega
  obtain ⟨rootsArena,unused,listArena,number,nextAligned,rounded⟩ := roots_geometry (chunksCursor ch) (kind.count data) (data.scratchBytes budget) 0 scratch fixed.aligned fits
  refine ⟨?_,rootsArena,listArena,nextAligned,?_⟩
  · cases kind with
    | transactions=>have a:=layout.transactionCountBound; have b:=layout.budgetBound; change data.transactionCount≤134217728; omega
    | withdrawals=>have a:=layout.withdrawalCountBound; have b:=layout.budgetBound; change data.withdrawalCount≤134217728; omega
  · exact AllocatedBytes.Arena.subrange ch 608 (32*kind.slot) 32 fixed.chunksArena (by cases kind <;> decide)

theorem arguments_read (kind : Kind) (data : Description) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ch : BitVec 64)
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (count : source.locals.lookup (ofString kind.name)=some (.val (.word (BitVec.ofNat 64 (kind.count data)))))
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) kind.arguments=
      some (PListChunks.values (chunksCursor ch) (kind.count data) (BitVec.ofNat 64 (kind.count data)) (ch+BitVec.ofNat 64 (32*kind.slot))) := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,Kind.arguments,listArguments,localVar,roots,count,chunks,PListChunks.values,valueIsWord,valueWord,wordOpHOL,wordOp]

/-- Actual original final root-list hash at its current row count and heap. -/
theorem call_cost (kind : Kind) (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (kind.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch)
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (count : source.locals.lookup (ofString kind.name)=some (.val (.word (BitVec.ofNat 64 (kind.count data)))))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source kind.call=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤115*kind.count data+24207 := by
  obtain ⟨bounded,rootsArena,listArena,aligned,outArena⟩ := current_geometry kind data lower upper budget ch layout geometry
  exact PListChunks.call_cost source post (chunksCursor ch) (kind.cursor data ch) (ch+BitVec.ofNat 64 (32*kind.slot)) (BitVec.ofNat 64 (kind.count data)) stp accel chunk zeros (kind.count data)
    bounded actual.ready.workspace actual.ready.heap rootsArena listArena aligned outArena (some none) kind.arguments (arguments_read kind data source ch roots count actual.ready.chunks) result run notTimeout

/-- Same real normal list hash restores its current cursor and preserves
all payload input/caller facts before the actual shared-scope release. -/
theorem call_normal (kind : Kind) (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (layout : data.Layout lower upper budget)
    (actual : StaticFields.State origin source lower upper data.payload data.raw ch out (kind.cursor data ch) mark stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) (separation : HashInput.Separation stp accel chunk lower) (small : lower<2^64) (before : upper≤ch.toNat)
    (roots : source.locals.lookup (ofString "roots")=some (.val (.word (chunksCursor ch))))
    (count : source.locals.lookup (ofString kind.name)=some (.val (.word (BitVec.ofNat 64 (kind.count data)))))
    (run : evaluateHOLFiniteState source kind.call=(none,post)) : StaticFields.State origin post lower upper data.payload data.raw ch out (kind.cursor data ch) mark stp accel chunk zeros := by
  obtain ⟨bounded,rootsArena,listArena,aligned,outArena⟩ := current_geometry kind data lower upper budget ch layout geometry
  have args := arguments_read kind data source ch roots count actual.ready.chunks
  have heap := PListChunks.ignored_return_heap source post (chunksCursor ch) (kind.cursor data ch) (ch+BitVec.ofNat 64 (32*kind.slot)) (BitVec.ofNat 64 (kind.count data)) stp accel chunk zeros (kind.count data)
    bounded actual.ready.workspace actual.ready.heap rootsArena listArena aligned outArena kind.arguments args run
  apply actual.after_call origin source post lower upper data.payload data.raw ch out (kind.cursor data ch) mark stp accel chunk zeros (ofString "htr_plist_chunks") kind.arguments run heap
  · intro key different
    exact GlobalEffects.call_body key source.code (some none) (ofString "htr_plist_chunks") kind.arguments PListChunks.formals PListChunks.body .one
      (PListChunks.original_code source.code actual.ready.workspace.sha.installed) (PListChunks.globals key source.code actual.ready.workspace.sha.installed different)
  · intro query low high
    have protection := separation.at_word source stp accel chunk zeros query lower actual.ready.workspace small low
    have static := (data.static_geometry lower upper budget ch layout geometry).1
    have below : query.toNat<ch.toNat := by omega
    have rootsAway := CopyGeneral.Away.after ch query 608 static.chunksAligned (by have h:=static.chunksArena.upper; omega) below
    have scratch := (data.static_geometry lower upper budget ch layout geometry).2.1
    have fits : rootsBytes (kind.count data)≤data.scratchBytes budget := by
      cases kind <;> simp only [Kind.count] <;> unfold rootsBytes Description.scratchBytes <;> omega
    have nextNumber : (kind.cursor data ch).toNat=(chunksCursor ch).toNat+rootsBytes (kind.count data) :=
      byteAddress_toNat (chunksCursor ch) (rootsBytes (kind.count data)) (by have h:=scratch.upper; omega)
    exact PListChunks.call_memory source post (chunksCursor ch) (kind.cursor data ch) (ch+BitVec.ofNat 64 (32*kind.slot)) (BitVec.ofNat 64 (kind.count data)) stp accel chunk zeros query (kind.count data)
      bounded protection actual.ready.heap rootsArena listArena aligned outArena (by rw [nextNumber]; have h:=static.chunksBefore; omega)
      (CopyGeneral.Away.subrange ch query 608 (32*kind.slot) 32 rootsAway (by cases kind <;> decide)) kind.arguments args run

end InitECandidate.Solver.Input.PayloadHash.ListPhase

#print axioms InitECandidate.Solver.Input.PayloadHash.ListPhase.current_geometry
#print axioms InitECandidate.Solver.Input.PayloadHash.ListPhase.arguments_read
#print axioms InitECandidate.Solver.Input.PayloadHash.ListPhase.call_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.ListPhase.call_normal
