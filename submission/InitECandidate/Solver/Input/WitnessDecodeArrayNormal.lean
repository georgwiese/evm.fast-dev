import InitECandidate.Solver.Input.WitnessDecodeSliceNormal
import InitECandidate.Solver.Input.WitnessDecodeArrayEntry
import InitECandidate.Solver.Input.WitnessStepParsedNormal

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Genuine whole original decode returns are classified without using a
cost-only stopping alternative: either the real empty node with a protected
scratch/global frame, or the actual array decision with its physical data. -/
theorem decode_array_normal (input : Guest.InputBlob)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (db pointer length cursor limit : BitVec 64)
    (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024)
    (inputAbove : 2713731432≤pointer.toNat) (below : cursor.toNat≤2713717616)
    (installed : OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (Mpt.WitnessStep.body .decode)=(some (.returned value),post)) :
    (value=.rStruct [.val (.word 0#64),.val (.word 0#64)] ∧
      Rlp.Validation.Arena post cursor limit ∧ Rlp.Validation.Above source post cursor.toNat ∧
      (∀ key,post.globals.lookup key=source.globals.lookup key)) ∨
      ∃ origin current header payload heap count items inner,
        DecodeSliceEntry input origin (bind current "arr" heap) db pointer length heap cursor limit header payload count items ∧
        Rlp.Validation.Above source origin cursor.toNat ∧
        (∀ key,origin.globals.lookup key=source.globals.lookup key) ∧
        origin.memaddrs=source.memaddrs ∧ origin.be=source.be ∧ origin.code=source.code ∧
        evaluateHOLFiniteState (bind current "arr" heap) Mpt.WitnessDecode.afterArray=(some (.returned value),inner) ∧
        post=restore source "it" (restore (Mpt.WitnessStep.tupleEntry source) "e" (restore origin "sl" (restore current "arr" inner))) := by
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
  obtain ⟨origin,middle,answer,nextBoundary,parsed,nextArena,above,domain,endian,codeEq,nextInstalled,globals,itemCell,nextDb,nextPointer,nextLength,continued,endpoint⟩:=
    step_parsed_normal .decode input source post db pointer length cursor limit originalBoundary dbCell pointerCell lengthCell arena below fits installed value normal
  have nextHeap : origin.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=(globals _).trans heapCell
  rcases decode_slice_entry_normal input origin middle db pointer length heap cursor limit answer nextBoundary parsed itemCell nextDb nextPointer nextLength nextArena
    nextHeap heapBound heapAligned beforeHeap before small inputAbove below nextInstalled value continued with empty|reached
  · obtain ⟨valueEq,middleEq⟩:=empty
    have finalArena : Rlp.Validation.Arena post cursor limit:=by
      apply Rlp.Validation.Arena.of_fields origin post cursor limit nextArena
      · rw [endpoint,middleEq]; rfl
      · rw [endpoint,middleEq]; rfl
    exact Or.inl ⟨valueEq,finalArena,by intro query lower; rw [endpoint,middleEq]; exact above query lower,
      by intro key; rw [endpoint,middleEq]; exact globals key⟩
  · obtain ⟨header,payload,count,items,current,last,entry,slicesRun,restored⟩:=reached
    obtain ⟨inner,arrayRun,restoredArray⟩:=entry.array_trace input origin current last db pointer length heap cursor limit header payload count items (some (.returned value)) slicesRun
    exact Or.inr ⟨origin,current,header,payload,heap,count,items,inner,entry.bind_array input origin current db pointer length heap cursor limit header payload count items,
      above,globals,domain,endian,codeEq,arrayRun,by rw [endpoint,restored,restoredArray]⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.decode_array_normal
