import InitECandidate.Solver.Input.Witness.ArraysEntry
import InitECandidate.Solver.Input.Witness.ControlFields

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 400000

private theorem total_number (bytes total : Nat) (small : bytes<2^64) (bound : total≤bytes) :
    (BitVec.ofNat 64 total).toNat=total := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]

private theorem entry_room (pointer bytes array total : Nat)
    (after : pointer+bytes+8≤array) (room : array+4*total≤33806089496) : pointer+bytes+8≤33806089496 := by omega

private theorem clock_eight (bytes clock : Nat) (enough : 6*bytes+28≤clock) : 8≤clock := by omega

private theorem remaining_clock (bytes clock paid : Nat) (enough : 6*bytes+28≤clock) (bound : paid≤8) :
    6*bytes+20≤clock-paid := by omega

/-- The actual witness offset loop, real validator, all offset loads and all
three byte-list calls compose. Offset validity and dictionary decoder data
are derived together, while preceding request decoding/layout remain explicit. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer offsetArray array si : BitVec 64) (start total : Nat)
    (environment : Environment source) (heap : Blob.HeapInput source input pointer)
    (minimum : 12≤total) (inside : start+total≤input.length%2^64)
    (wp : source.locals.lookup (ofString "wp")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (wlen : source.locals.lookup (ofString "wlen")=some (.val (.word (BitVec.ofNat 64 total))))
    (offsets : source.globals.lookup (ofString "ssz_offs")=some (.val (.word offsetArray)))
    (pointerLower : 2701131776≤pointer.toNat) (pointerAligned : pointer.toNat%8=0)
    (offsetAligned : offsetArray.toNat%8=0) (offsetLower : 2701131776≤offsetArray.toNat)
    (offsetBefore : offsetArray.toNat+24≤pointer.toNat)
    (arrayAligned : array.toNat%8=0) (arrayAfter : pointer.toNat+input.length%2^64+8≤array.toNat)
    (room : array.toNat+4*total≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (offsetCode : source.code.lookup (ofString "ssz_check_offsets")=some (Offsets.formals,Offsets.body,.one))
    (siLocal : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (siArena : Arena si 96) (siAligned : si.toNat%8=0) (siAfter : pointer.toNat+input.length%2^64+8≤si.toNat)
    (siBefore : si.toNat+96≤array.toNat)
    (enough : 6*(input.length%2^64)+28≤source.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source offsetBody=(some (.returned value),post)) :
    offsetNat input start 0=12 ∧ 12≤offsetNat input start 1 ∧
      offsetNat input start 1≤offsetNat input start 2 ∧ offsetNat input start 2≤total ∧
      ∃ loadedSource innerPost paid,
        let ready:=loadedState loadedSource input start
        paid≤8 ∧ ready.clock=source.clock-paid ∧ BackingLayout.control ready=BackingLayout.control source ∧
          ArraysResult ready innerPost input pointer array si start (offsetNat input start 0) (offsetNat input start 1) (offsetNat input start 2) total value ∧
          post=restore source "i" (restoreLoaded loadedSource input start innerPost) ∧
          post.memory=innerPost.memory ∧ post.globals=innerPost.globals ∧ post.clock=innerPost.clock := by
  classical
  have totalNumber := total_number (input.length%2^64) total (Nat.mod_lt _ (by decide))
    ((Nat.le_add_left total start).trans inside)
  have prefixExtent : start+12≤input.length%2^64:=(Nat.add_le_add_left minimum start).trans inside
  have pointerRoom:=entry_room pointer.toNat (input.length%2^64) array.toNat total arrayAfter room
  obtain ⟨first,middleLower,ordered,lastUpper,loadedSource,innerPost,paid,bound,clock,control,readyHeap,other,w0,w1,w2,frame,readyRun,postEq⟩:=
    arrays_entry source post input pointer offsetArray (BitVec.ofNat 64 total) start heap prefixExtent wp wlen offsets environment.domain pointerAligned
      offsetAligned offsetLower offsetBefore pointerRoom offsetCode environment.failCode environment.exceptionShape (clock_eight _ _ enough) value run
  have lastBound:=lastUpper.trans_eq totalNumber
  let ready:=loadedState loadedSource input start
  have readyEnvironment:=Environment.of_control source ready control environment
  have readyWp:=(other (ofString "wp") (by decide)).trans wp
  have readyWlen:=(other (ofString "wlen") (by decide)).trans wlen
  have readySi:=(other (ofString "si") (by decide)).trans siLocal
  have readyHeapGlobal:=global_of_control source ready (ofString "heap_ptr") (.val (.word array)) control heapGlobal
  have firstBefore:=first.le.trans middleLower
  have readyEnough:=(remaining_clock _ _ _ enough bound).trans_eq clock.symm
  have arrays:=arrays_normal ready innerPost input pointer array si start (offsetNat input start 0) (offsetNat input start 1) (offsetNat input start 2) total
    readyEnvironment readyHeap ⟨firstBefore,ordered,lastBound⟩ inside pointerLower pointerAligned arrayAligned arrayAfter room readyHeapGlobal
    readyWp w0 w1 w2 readyWlen readySi siArena siAligned siAfter siBefore readyEnough value readyRun
  refine ⟨first,middleLower,ordered,lastBound,loadedSource,innerPost,paid,bound,clock,control,arrays,postEq,?_,?_,?_⟩
  · have memory:=congrArg (fun state=>state.memory) postEq
    exact memory
  · have globals:=congrArg (fun state=>state.globals) postEq
    exact globals
  · have clocks:=congrArg (fun state=>state.clock) postEq
    exact clocks

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.body_normal
