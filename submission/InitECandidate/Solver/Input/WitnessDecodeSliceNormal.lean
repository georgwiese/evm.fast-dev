import InitECandidate.Solver.Input.WitnessDecodeSliceEntry
import InitECandidate.Solver.Rlp.SlicesSnapshotNormal

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Genuine post-parser normal returns either produce the literal empty
node at unchanged nonlocals or pass the real list converter with its actual
physical array. The cost trace's stopping alternative is not used here. -/
theorem decode_slice_entry_normal (input : Guest.InputBlob)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) (answer : ValueHOL 64)
    (boundary : RootBoundary input source) (parsed : Rlp.Decode.Complete pointer length answer)
    (itemCell : source.locals.lookup (ofString "it")=some answer)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat) (beforeDb : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024)
    (inputAbove : 2713731432≤pointer.toNat) (below : cursor.toNat≤2713717616)
    (installed : OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (Mpt.WitnessStep.afterRlp .decode)=(some (.returned value),post)) :
    (value=.rStruct [.val (.word 0#64),.val (.word 0#64)] ∧ post=emptyLocalsHOLFinite source) ∨
      ∃ header payload count items ready inner,
        DecodeSliceEntry input source ready db pointer length heap cursor limit header payload count items ∧
        evaluateHOLFiniteState ready Mpt.WitnessDecode.afterSlices=(some (.returned value),inner) ∧ post=restore source "sl" inner := by
  obtain ⟨header,payload,flag,answerEq,headerBound,positive,extent,binary,listHeader⟩:=parsed
  rw [answerEq] at itemCell
  have guardRun:=Mpt.WitnessDecode.string_guard_execute source pointer header payload flag itemCell
  by_cases zero : flag=0#64
  · have stops : (evaluateHOLFiniteState source Mpt.WitnessDecode.stringGuard).1≠none:=by
      rw [guardRun,if_pos zero]
      exact Mpt.WitnessDecode.string_body_no_pass source installed
    rw [Mpt.WitnessDecode.suffix_shape,Input.sequence_stopped source Mpt.WitnessDecode.stringGuard Mpt.WitnessDecode.slicesCall stops,
      guardRun,if_pos zero] at normal
    obtain ⟨payloadZero,valueEq,postEq⟩:=Mpt.WitnessDecode.string_body_normal source post pointer header payload flag itemCell value normal
    exact Or.inl ⟨valueEq,postEq⟩
  · have flagEq:=binary.resolve_left zero
    subst flag
    rw [if_neg zero] at guardRun
    rw [Mpt.WitnessDecode.suffix_shape,evaluateHOLFiniteState_seq_line780,guardRun,Mpt.WitnessDecode.slices_shape] at normal
    have pointerNumber : (pointer+header).toNat=pointer.toNat+header.toNat:=
      BitVec.toNat_add_of_lt (by have upper:=heap.isLt; omega)
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) Mpt.WitnessDecode.slicesArguments=
        some (Rlp.Header.values (pointer+header) payload):=by
      simp [Mpt.WitnessDecode.slicesArguments,Mpt.WitnessDecode.field,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,itemCell,Rlp.Item.result]
    obtain ⟨funded,target,items,count,inner,snapshot,continued,endpoint⟩:=Rlp.Slices.scoped_snapshot_normal source post (pointer+header) payload heap cursor limit 2713717616
      "sl" Mpt.WitnessDecode.slicesArguments Mpt.WitnessDecode.afterSlices args arena heapCell heapBound heapAligned
      (by rw [pointerNumber]; omega) (by omega) (by decide) below (by rw [pointerNumber]; omega) installed value normal
    let ready:=CallNormal.continuationEntry source target "sl" (Rlp.Slices.result heap count)
    have physical:=snapshot.resumed source target (pointer+header) payload heap cursor limit count items "sl"
    have retained (name : String) (different : ofString "sl"≠ofString name) :
        ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
      CallNormal.continuation_lookup_other source target "sl" name _ different
    have currentBoundary:=boundary.slices_frame input source ready (pointer+header) payload heap cursor limit count items heapCell below physical (retained "db" (by decide))
    have currentInstalled : OriginalCode.Installed ready.code:=by
      have codeEq:=physical.code
      change ready.code=source.code at codeEq
      rw [codeEq]
      exact installed
    have entry : DecodeSliceEntry input source ready db pointer length heap cursor limit header payload count items:=
      ⟨⟨header,payload,1#64,rfl,headerBound,positive,extent,Or.inr rfl,listHeader⟩,extent,pointerNumber,heapCell,before,beforeDb,inputAbove,small,physical,currentBoundary,currentInstalled,
        (retained "db" (by decide)).trans dbCell,(retained "p" (by decide)).trans pointerCell,(retained "n" (by decide)).trans lengthCell,
        (retained "it" (by decide)).trans itemCell,CallNormal.continuation_lookup_same source target "sl" _⟩
    exact Or.inr ⟨header,payload,count,items,ready,inner,entry,continued,endpoint⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.decode_slice_entry_normal
