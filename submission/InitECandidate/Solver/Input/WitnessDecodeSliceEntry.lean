import InitECandidate.Solver.Input.RootBoundarySlicesFrame
import InitECandidate.Solver.Mpt.WitnessDecodeStringTrace

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Physical data at the actual original decode continuation after its
list converter has returned. All fields describe the same reached state. -/
structure DecodeSliceEntry (input : Guest.InputBlob)
    (origin current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit header payload count : BitVec 64)
    (items : List Rlp.ListItem) : Prop where
  complete : Rlp.Decode.Complete pointer length (Rlp.Item.result pointer header payload 1#64)
  extent : header.toNat+payload.toNat=length.toNat
  pointerNumber : (pointer+header).toNat=pointer.toNat+header.toNat
  sourceHeap : origin.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  inputBeforeHeap : pointer.toNat+length.toNat≤heap.toNat
  inputBeforeDb : pointer.toNat+length.toNat≤db.toNat
  inputLower : 2713731432≤pointer.toNat
  lengthBound : length.toNat≤1024
  snapshot : Rlp.Slices.Snapshot (LocalEffects.erase origin) current (pointer+header) payload heap cursor limit count items
  boundary : RootBoundary input current
  installed : OriginalCode.Installed current.code
  dbCell : current.locals.lookup (ofString "db")=some (.val (.word db))
  pointerCell : current.locals.lookup (ofString "p")=some (.val (.word pointer))
  lengthCell : current.locals.lookup (ofString "n")=some (.val (.word length))
  itemCell : current.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload 1#64)
  sliceCell : current.locals.lookup (ofString "sl")=some (Rlp.Slices.result heap count)

/-- Every actual post-parser outcome stops within the list allowance or
reaches the original suffix with its genuine allocated row array and both
databases retained. No successful list conversion is an input assumption. -/
theorem decode_slice_entry_trace (input : Guest.InputBlob)
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
    (installed : OriginalCode.Installed source.code) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (Mpt.WitnessStep.afterRlp .decode)=(outcome,post)) :
    source.clock-post.clock≤71*length.toNat+35 ∨
      ∃ header payload count items ready inner,
        DecodeSliceEntry input source ready db pointer length heap cursor limit header payload count items ∧
        ready.clock≤source.clock ∧ source.clock-ready.clock≤71*length.toNat+35 ∧
        evaluateHOLFiniteState ready Mpt.WitnessDecode.afterSlices=(outcome,inner) ∧
        post=QueryBranch.restore source "sl" inner := by
  obtain ⟨header,payload,flag,answerEq,headerBound,positive,extent,binary,listHeader⟩:=parsed
  rw [answerEq] at itemCell
  rcases Mpt.WitnessDecode.slices_trace source post pointer header payload flag itemCell binary installed outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨flagEq,slicesRun⟩:=reached
    subst flag
    have pointerNumber : (pointer+header).toNat=pointer.toNat+header.toNat:=
      BitVec.toNat_add_of_lt (by have upper:=heap.isLt; omega)
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) Mpt.WitnessDecode.slicesArguments=
        some (Rlp.Header.values (pointer+header) payload):=by
      simp [Mpt.WitnessDecode.slicesArguments,Mpt.WitnessDecode.field,Rlp.Header.values,
        evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,itemCell,Rlp.Item.result]
    rw [Mpt.WitnessDecode.slices_shape] at slicesRun
    rcases Rlp.Slices.scoped_snapshot_trace source post (pointer+header) payload heap cursor limit 2713717616
        "sl" Mpt.WitnessDecode.slicesArguments Mpt.WitnessDecode.afterSlices args arena heapCell heapBound heapAligned
        (by rw [pointerNumber]; omega) (by omega) (by decide) below (by rw [pointerNumber]; omega) installed outcome slicesRun with stopped|reached
    · exact Or.inl (by omega)
    · obtain ⟨target,items,count,inner,snapshot,funded,forward,price,continued,endpoint⟩:=reached
      let ready:=CallNormal.continuationEntry source target "sl" (Rlp.Slices.result heap count)
      have physical:=snapshot.resumed source target (pointer+header) payload heap cursor limit count items "sl"
      have retained (name : String) (different : ofString "sl"≠ofString name) :
          ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
        CallNormal.continuation_lookup_other source target "sl" name _ different
      have nextDb : ready.locals.lookup (ofString "db")=some (.val (.word db)):=
        (retained "db" (by decide)).trans dbCell
      have currentBoundary:=boundary.slices_frame input source ready (pointer+header) payload heap cursor limit count items heapCell below physical
        (retained "db" (by decide))
      have currentCode : OriginalCode.Installed ready.code:=by
        have codeEq:=physical.code
        change ready.code=source.code at codeEq
        rw [codeEq]
        exact installed
      have entry : DecodeSliceEntry input source ready db pointer length heap cursor limit header payload count items:=
        ⟨⟨header,payload,1#64,rfl,headerBound,positive,extent,Or.inr rfl,listHeader⟩,extent,pointerNumber,heapCell,before,beforeDb,inputAbove,small,physical,
          currentBoundary,currentCode,nextDb,(retained "p" (by decide)).trans pointerCell,(retained "n" (by decide)).trans lengthCell,
          (retained "it" (by decide)).trans itemCell,CallNormal.continuation_lookup_same source target "sl" _⟩
      exact Or.inr ⟨header,payload,count,items,ready,inner,entry,forward,by change source.clock-target.clock≤_; omega,continued,endpoint⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.decode_slice_entry_trace
