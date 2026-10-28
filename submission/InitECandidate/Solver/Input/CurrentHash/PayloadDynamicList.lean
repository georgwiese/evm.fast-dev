import InitECandidate.Solver.Input.CurrentHash.PayloadStateCalls
import InitECandidate.Solver.Input.CurrentHash.PListMemory

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}

theorem State.list_arguments (data : State input source blob record array ch cursor chunk out zeros length start size)
    (countName : String) (slot n : Nat) (roots : BitVec 64)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (count : source.locals.lookup (ofString countName)=some (.val (.word (BitVec.ofNat 64 n)))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (listArguments countName slot)=
      some (PListCost.values roots (BitVec.ofNat 64 n) (ch+BitVec.ofNat 64 (32*slot)) n) := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,listArguments,localVar,root,count,data.chunks,PListCost.values,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem State.list_frame (data : State input source blob record array ch cursor chunk out zeros length start size)
    (countName : String) (slot n : Nat) (roots query : BitVec 64) (bounded : n≤134217728) (slotBound : slot<19)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (count : source.locals.lookup (ofString countName)=some (.val (.word (BitVec.ofNat 64 n))))
    (rootsArena : AllocatedBytes.Arena roots (32*n)) (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32)
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_plist_chunks") (listArguments countName slot))=(none,post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) :=
  PListMemory.call_frame source post roots cursor (BitVec.ofNat 64 n) chunk (ch+BitVec.ofNat 64 (32*slot)) zeros query n
    (data.query_context query before) bounded rootsArena (data.output_arena slot slotBound) (data.output_away slot slotBound query before)
    data.chunkCell data.chunkArena data.chunkAligned chunkAway (listArguments countName slot) (data.list_arguments countName slot n roots root count) actual

theorem State.after_list (data : State input source blob record array ch cursor chunk out zeros length start size)
    (countName : String) (slot n : Nat) (roots : BitVec 64) (bounded : n≤134217728) (slotBound : slot<19)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (count : source.locals.lookup (ofString countName)=some (.val (.word (BitVec.ofNat 64 n)))) (rootsArena : AllocatedBytes.Arena roots (32*n))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_plist_chunks") (listArguments countName slot))=(none,post)) :
    State input post blob record array ch cursor chunk out zeros length start size := by
  apply data.after_call .htr_plist_chunks (listArguments countName slot) actual
  intro query lower upper
  exact data.list_frame countName slot n roots query bounded slotBound root count rootsArena upper (data.chunk_away query lower) actual

theorem State.list_cost (data : State input source blob record array ch cursor chunk out zeros length start size)
    (countName : String) (slot n : Nat) (roots : BitVec 64) (bounded : n≤134217728)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (count : source.locals.lookup (ofString countName)=some (.val (.word (BitVec.ofNat 64 n))))
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_plist_chunks") (listArguments countName slot))=(result,post))
    (notTimeout : result≠some .timeOut) : source.clock-post.clock≤88*n+3169 :=
  PListCost.call_cost source post roots (BitVec.ofNat 64 n) (ch+BitVec.ofNat 64 (32*slot)) n bounded data.context.installed
    (some none) (listArguments countName slot) (data.list_arguments countName slot n roots root count) result actual notTimeout

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.list_arguments
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.list_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_list
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.list_cost
