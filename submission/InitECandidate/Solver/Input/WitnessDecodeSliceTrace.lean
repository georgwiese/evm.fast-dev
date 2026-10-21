import InitECandidate.Solver.Input.WitnessDecodeSliceEntry
import InitECandidate.Solver.Input.WitnessStepParsedSuffix

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The complete original237 prefix, including its real caught parser,
list/string decision and array conversion. Every outcome stops within the
prefix allowance or reaches the genuine suffix with current physical data.
The input extent is below the actual immutable node database, so both
scratch separation and the incoming heap bound follow from main's data. -/
theorem decode_slices_trace (input : Guest.InputBlob)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length cursor limit : BitVec 64)
    (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024)
    (inputAbove : 2713731432≤pointer.toNat) (below : cursor.toNat≤2713717616)
    (installed : OriginalCode.Installed source.code) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (Mpt.WitnessStep.body .decode)=(outcome,post)) :
    source.clock-post.clock≤131*length.toNat+79 ∨
      ∃ origin header payload heap count items ready inner,
        DecodeSliceEntry input origin ready db pointer length heap cursor limit header payload count items ∧
        Rlp.Validation.Above source origin cursor.toNat ∧
        (∀ key,origin.globals.lookup key=source.globals.lookup key) ∧
        ready.clock≤source.clock ∧ source.clock-ready.clock≤131*length.toNat+79 ∧
        evaluateHOLFiniteState ready Mpt.WitnessDecode.afterSlices=(outcome,inner) ∧
        post=QueryBranch.restore source "it" (QueryBranch.restore (Mpt.WitnessStep.tupleEntry source) "e" (QueryBranch.restore origin "sl" inner)) := by
  have originalBoundary:=boundary
  obtain ⟨codeArray,nodes,codes,heap,nodeDatabase,codeDatabase,nodeCell,heapCell,heapArena,heapAligned,nodeBefore,codeBefore⟩:=boundary
  have nodeEq : nodes=db:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (nodeCell.symm.trans dbCell)))
  subst nodes
  have tableBefore : db.toNat≤heap.toNat:=by
    obtain ⟨capacity,capacityCell,bound⟩:=nodeBefore
    omega
  have beforeHeap : pointer.toNat+length.toNat≤heap.toNat:=before.trans tableBefore
  have fits : pointer.toNat+length.toNat<2^64:=by have upper:=heap.isLt; omega
  have heapBound : heap.toNat≤33806089496:=by have upper:=heapArena.upper; omega
  rcases step_parsed_suffix .decode input source post db pointer length cursor limit originalBoundary dbCell pointerCell lengthCell arena below fits installed outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨origin,middle,answer,nextBoundary,parsed,nextArena,above,domain,endian,codeEq,nextInstalled,globalCells,itemCell,nextDb,nextPointer,nextLength,forward,price,continued,endpoint⟩:=reached
    have nextHeap : origin.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=
      (globalCells _).trans heapCell
    rcases decode_slice_entry_trace input origin middle db pointer length heap cursor limit answer nextBoundary parsed itemCell
        nextDb nextPointer nextLength nextArena nextHeap heapBound heapAligned beforeHeap small inputAbove below nextInstalled outcome continued with stopped|reached
    · have remainingForward:=evaluateHOLFiniteState_clock_le origin (Mpt.WitnessStep.afterRlp .decode)
      rw [continued] at remainingForward
      change middle.clock≤origin.clock at remainingForward
      have finalClock : post.clock=middle.clock:=by rw [endpoint]; rfl
      rw [finalClock]
      exact Or.inl (by omega)
    · obtain ⟨header,payload,count,items,ready,inner,entry,nextForward,nextPrice,tail,restored⟩:=reached
      have currentForward : ready.clock≤source.clock:=nextForward.trans forward
      have totalPrice : source.clock-ready.clock≤131*length.toNat+79:=by omega
      exact Or.inr ⟨origin,header,payload,heap,count,items,ready,inner,entry,above,globalCells,currentForward,totalPrice,tail,by rw [endpoint,restored]⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.decode_slices_trace
