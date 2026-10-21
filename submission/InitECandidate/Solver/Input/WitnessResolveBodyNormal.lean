import InitECandidate.Solver.Input.WitnessResolveNormalFrame
import InitECandidate.Solver.Input.WitnessStepParsedNormal
import InitECandidate.Solver.Mpt.WitnessResolveSuffixNormal

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Genuine whole original236 returns have a restored physical scratch
arena and protect every older word above its cursor. Results are exactly
empty, the real fresh hashed node, or a bounded next decode slice. Pending
hash pointers, including those in fresh nodes, are actual32-byte input spans. -/
theorem resolve_body_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length cursor limit : BitVec 64) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤2713717616)
    (small : length.toNat≤1024) (inputLower : 2713731432≤pointer.toNat) (before : pointer.toNat+length.toNat≤db.toNat)
    (installed : OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (Mpt.WitnessStep.body .resolve)=(some (.returned value),post)) :
    ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      AllocatedBytes.Arena heap 0 ∧ heap.toNat%8=0 ∧ ResolveFrame source post heap cursor limit ∧
      ((value=.rStruct [.val (.word 0#64),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)]) ∨
       (value=.rStruct [.val (.word 0#64),.val (.word heap),.val (.word 0#64),.val (.word 0#64)] ∧
         AllocatedBytes.Arena heap 32 ∧ post.memory heap=.word 0#64 ∧
         ∃ hash,2713731432≤hash.toNat ∧ hash.toNat+32≤db.toNat ∧ post.memory (heap+24#64)=.word hash) ∨
       ∃ nextPointer nextLength pending,
         value=.rStruct [.val (.word 1#64),.val (.word nextPointer),.val (.word nextLength),.val (.word pending)] ∧
         nextLength.toNat≤1024 ∧ 2713731432≤nextPointer.toNat ∧ nextPointer.toNat+nextLength.toNat≤db.toNat ∧
         (pending=0#64 ∨ 2713731432≤pending.toNat ∧ pending.toNat+32≤db.toNat)) := by
  have originalBoundary:=boundary
  obtain ⟨codeArray,nodes,codes,heap,nodeDatabase,codeDatabase,nodeCell,heapCell,heapArena,heapAligned,nodeBefore,codeBefore⟩:=boundary
  have nodeEq : nodes=db:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (nodeCell.symm.trans dbCell)))
  subst nodes
  have fits : pointer.toNat+length.toNat<2^64:=before.trans_lt db.isLt
  obtain ⟨ready,inner,answer,nextBoundary,parsed,nextArena,above,domain,endian,codeEq,nextInstalled,globals,itemCell,nextDb,nextPointer,nextLength,continued,endpoint⟩:=
    step_parsed_normal .resolve input source post db pointer length cursor limit originalBoundary dbCell pointerCell lengthCell arena below fits installed value normal
  obtain ⟨header,payload,flag,answerEq,headerSmall,positive,extent,binary,listHeader⟩:=parsed
  rw [answerEq] at itemCell
  have nextHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=(globals _).trans heapCell
  obtain ⟨codeArray2,nodes2,codes2,heap2,nodeDatabase2,codeDatabase2,nodeCell2,heapCell2,heapArena2,heapAligned2,nodeBefore2,codeBefore2⟩:=nextBoundary
  have nodeEq2 : nodes2=db:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (nodeCell2.symm.trans nextDb)))
  subst nodes2
  have classified:=Mpt.WitnessResolve.suffix_normal ready inner _ db 2713717584#64 pointer length header payload flag heap
    (WitnessConstructors.nodeCount input) (WitnessConstructors.nodeSlices input) nodeDatabase2 nextDb nextPointer nextLength itemCell nextHeap heapArena heapAligned
    small inputLower before nextInstalled value continued
  have finalPure : LocalEffects.erase post=LocalEffects.erase inner:=by rw [endpoint]; rfl
  have lift (frame : ResolveFrame ready inner heap cursor limit) : ResolveFrame source post heap cursor limit:=
    (frame.prefix source ready inner heap cursor limit domain endian codeEq globals above).of_erase source post inner heap cursor limit finalPure
  have hash_span (thirtyTwo : payload=32#64) :
      2713731432≤(pointer+header).toNat ∧ (pointer+header).toNat+32≤db.toNat := by
    have number : (pointer+header).toNat=pointer.toNat+header.toNat:=
      BitVec.toNat_add_of_lt (by omega)
    rw [thirtyTwo] at extent
    change header.toNat+32≤length.toNat at extent
    rw [number]
    omega
  rcases classified with ⟨valueEq,pure⟩|⟨valueEq,thirtyTwo,nodeArena,pure⟩|⟨nextPointer,nextLength,pending,valueEq,nextSmall,nextLower,nextBefore,pendingEq,pure⟩
  · exact ⟨heap,heapCell,heapArena,heapAligned,
      lift (ResolveFrame.unchanged ready inner heap cursor limit nextHeap heapArena heapAligned nextArena pure),Or.inl valueEq⟩
  · have frame:=ResolveFrame.hashed ready inner heap (pointer+header) cursor limit nodeArena heapAligned nextArena pure
    have memory:=LocalEffects.memory_of_erase (Mpt.WitnessResolve.hashAllocated ready heap (pointer+header)) post (finalPure.trans pure)
    have tag : post.memory heap=.word 0#64:=by
      rw [memory]
      exact Mpt.WitnessResolve.hash_allocated_tag ready heap (pointer+header)
    have hashCell : post.memory (heap+24#64)=.word (pointer+header):=by
      rw [memory]
      exact Mpt.WitnessResolve.hash_allocated_hash ready heap (pointer+header)
    exact ⟨heap,heapCell,heapArena,heapAligned,lift frame,Or.inr (Or.inl ⟨valueEq,nodeArena,tag,pointer+header,(hash_span thirtyTwo).1,(hash_span thirtyTwo).2,hashCell⟩)⟩
  · have pendingSpan : pending=0#64 ∨ 2713731432≤pending.toNat ∧ pending.toNat+32≤db.toNat:=by
      rcases pendingEq with zero|⟨same,thirtyTwo⟩
      · exact Or.inl zero
      · rw [same]
        exact Or.inr (hash_span thirtyTwo)
    exact ⟨heap,heapCell,heapArena,heapAligned,
      lift (ResolveFrame.unchanged ready inner heap cursor limit nextHeap heapArena heapAligned nextArena pure),
      Or.inr (Or.inr ⟨nextPointer,nextLength,pending,valueEq,nextSmall,nextLower,nextBefore,pendingSpan⟩)⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.resolve_body_normal
