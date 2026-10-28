import InitECandidate.Solver.Input.CurrentHash.PayloadStateRelease

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Earlier actual parent frontier retained by a local heap mark. Its numeric
facts survive temporary allocations; it is not a promise of additional room. -/
structure SavedCursor (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (ch mark : BitVec 64) : Prop where
  binding : source.locals.lookup (ofString name)=some (.val (.word mark))
  lower : 2701131776≤mark.toNat
  upper : mark.toNat≤2952790016
  aligned : mark.toNat%8=0
  afterChunks : ch.toNat+608≤mark.toNat

theorem SavedCursor.of_lookup {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {name : String} {ch mark : BitVec 64}
    (data : SavedCursor source name ch mark) (binding : post.locals.lookup (ofString name)=some (.val (.word mark))) : SavedCursor post name ch mark :=
  ⟨binding,data.lower,data.upper,data.aligned,data.afterChunks⟩

theorem State.saved_cursor {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size) (name : String)
    (binding : source.locals.lookup (ofString name)=some (.val (.word cursor))) : SavedCursor source name ch cursor :=
  ⟨binding,data.context.heapLower,data.context.heapBound,data.context.aligned,data.afterChunks⟩

theorem SavedCursor.after_call {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {name : String} {ch mark : BitVec 64}
    (data : SavedCursor source name ch mark) (function : MlS) (arguments : List (ExpHOL 64))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) function arguments)=(none,post)) : SavedCursor post name ch mark :=
  data.of_lookup ((CallNormal.ignored_lookup source post (ofString name) function arguments actual).trans data.binding)

theorem SavedCursor.after_program {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {name : String} {ch mark : BitVec 64}
    (data : SavedCursor source name ch mark) (program : ProgHOL 64) (safe : LocalPrefix (ofString name) program)
    (actual : evaluateHOLFiniteState source program=(none,post)) : SavedCursor post name ch mark := by
  have summary := safe.summary_full source
  unfold LocalSummary at summary
  rw [actual] at summary
  exact data.of_lookup ((summary.1 rfl).trans data.binding)

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.saved_cursor
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.SavedCursor.after_call
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.SavedCursor.after_program
