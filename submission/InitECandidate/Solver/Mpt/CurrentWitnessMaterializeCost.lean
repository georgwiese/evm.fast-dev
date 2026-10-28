import InitECandidate.Solver.Mpt.CurrentWitnessCoreCost
import InitECandidate.Solver.Mpt.WitnessMaterializeWrapperProgram
import InitECandidate.Solver.Input.ClockCostCaughtAssigned
import InitECandidate.Solver.Input.WordQuadEnvironment

namespace InitECandidate.Solver.Mpt.WitnessWrapper
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def seeded (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind (bind source "e" 0#64) "nd" 0#64

theorem seeded_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (notError : ofString "e"≠ofString name) (notNode : ofString "nd"≠ofString name) :
    (seeded source).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "nd" name 0#64 notNode).trans (bind_lookup_other source "e" name 0#64 notError)

theorem seeded_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (continuation : ProgHOL 64) (price : Nat)
    (tail : (seeded source).clock-(evaluateHOLFiniteState (seeded source) continuation).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (.dec (ofString "e") .one (.const 0#64)
      (.dec (ofString "nd") .one (.const 0#64) continuation))).2.clock≤price :=
  ClockCost.declared_current source "e" (.const 0#64) 0#64 _ price rfl
    (ClockCost.declared_current (bind source "e" 0#64) "nd" (.const 0#64) 0#64 continuation price rfl tail)

end InitECandidate.Solver.Mpt.WitnessWrapper

namespace InitECandidate.Solver.Mpt.WitnessMaterializeMpt
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem current_caught_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source caught).2.clock≤200225 := by
  obtain ⟨callee,called,dbLocal,pointerLocal,lengthLocal⟩:=word_triple_environment source.code.lookup
    (ofString "_decode_witness_node_body") (ofString "db") (ofString "p") (ofString "n") WitnessCore.body .one
    db pointer length (by decide) (by decide) (by decide) (WitnessCore.original_code source.code arena.code)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) childArguments=
      some [.val (.word db),.val (.word pointer),.val (.word length)] := by
    simp [childArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,dbCell,pointerCell,lengthCell]
  exact ClockCost.caught_destination_current source (some (.local,ofString "nd")) (ofString "_decode_witness_node_body") childArguments _
    WitnessCore.body callee .one (ofString "MptErr") (ofString "e") handler 200223 1 args called
    (WitnessCore.current_body_literal_price (callEntryStateHOLFinite source callee) db pointer length heap dbLocal pointerLocal lengthLocal
      small before heapCell heapArena heapBound aligned (arena.of_frame rfl)) (handler_price source.code arena.code)

/-- The current MPT catch wrapper includes its real release-and-rethrow
handler on every outcome, including failed calls and exhausted clocks. -/
theorem current_body_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤200225 := by
  let ready:=WitnessWrapper.seeded source
  have price:=current_caught_price ready db pointer length heap
    ((WitnessWrapper.seeded_other source "db" (by decide) (by decide)).trans dbCell)
    ((WitnessWrapper.seeded_other source "p" (by decide) (by decide)).trans pointerCell)
    ((WitnessWrapper.seeded_other source "n" (by decide) (by decide)).trans lengthCell)
    small before heapCell heapArena heapBound aligned (arena.of_frame rfl)
  have suffix:=ClockCost.sequence_current ready caught footer 200225 0 price (ClockCost.returned _ (localVar "nd"))
  rw [wrapper_shape,afterError]
  exact WitnessWrapper.seeded_price source afterResult 200225 (Nat.le_trans suffix (by omega))

end InitECandidate.Solver.Mpt.WitnessMaterializeMpt

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem current_caught_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap mark : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (markCell : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source caught).2.clock≤200227 := by
  obtain ⟨callee,called,dbLocal,pointerLocal,lengthLocal,markLocal⟩:=word_quad_environment source.code.lookup
    (ofString "_decode_witness_node_mpt") (ofString "db") (ofString "p") (ofString "n") (ofString "mark") WitnessMaterializeMpt.body .one
    db pointer length mark (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (WitnessMaterializeMpt.original_code source.code arena.code)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) childArguments=
      some [.val (.word db),.val (.word pointer),.val (.word length),.val (.word mark)] := by
    simp [childArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,dbCell,pointerCell,lengthCell,markCell]
  exact ClockCost.caught_destination_current source (some (.local,ofString "nd")) (ofString "_decode_witness_node_mpt") childArguments _
    WitnessMaterializeMpt.body callee .one (ofString "RlpErr") (ofString "e") handler 200225 1 args called
    (WitnessMaterializeMpt.current_body_price (callEntryStateHOLFinite source callee) db pointer length heap dbLocal pointerLocal lengthLocal
      small before heapCell heapArena heapBound aligned (arena.of_frame rfl)) (handler_price source.code arena.code)

theorem current_after_mark_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap mark : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (markCell : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source afterMark).2.clock≤200228 := by
  let ready:=WitnessWrapper.seeded source
  have price:=current_caught_price ready db pointer length heap mark
    ((WitnessWrapper.seeded_other source "db" (by decide) (by decide)).trans dbCell)
    ((WitnessWrapper.seeded_other source "p" (by decide) (by decide)).trans pointerCell)
    ((WitnessWrapper.seeded_other source "n" (by decide) (by decide)).trans lengthCell)
    ((WitnessWrapper.seeded_other source "mark" (by decide) (by decide)).trans markCell)
    small before heapCell heapArena heapBound aligned (arena.of_frame rfl)
  have suffix:=ClockCost.sequence_current ready caught footer 200227 1 price (footer_price ready.code arena.code)
  exact WitnessWrapper.seeded_price source afterResult 200228 suffix

/-- Whole unchanged current238 with its actual scratch mark, both catch
wrappers, release handlers and final release. A successful decode is never
assumed; all helper and short-clock outcomes fit the same allowance. -/
theorem current_body_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤200229 := by
  by_cases zero : source.clock=0
  · simp [zero]
  · let ready:=bind {source with clock:=source.clock-1} "mark" 2701127680#64
    have marked:=Arenas.mark_call source .down "mark" 2701127680#64 afterMark (Arenas.Scratch.mark_code source.code arena.code) arena.scratch (by omega)
    simp only [Arenas.markName] at marked
    rw [wrapper_shape,marked]
    change source.clock-(evaluateHOLFiniteState ready afterMark).2.clock≤200229
    have price:=current_after_mark_price ready db pointer length heap 2701127680#64
      ((bind_lookup_other _ "mark" "db" _ (by decide)).trans dbCell)
      ((bind_lookup_other _ "mark" "p" _ (by decide)).trans pointerCell)
      ((bind_lookup_other _ "mark" "n" _ (by decide)).trans lengthCell) (bind_lookup_same _ _ _)
      small before heapCell heapArena heapBound aligned (arena.of_frame rfl)
    change source.clock-1-(evaluateHOLFiniteState ready afterMark).2.clock≤200228 at price
    omega

end InitECandidate.Solver.Mpt.WitnessMaterialize

#print axioms InitECandidate.Solver.Mpt.WitnessMaterializeMpt.current_body_price
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.current_body_price
