import InitECandidate.Solver.Input.WitnessResolveResult
import InitECandidate.Solver.Mpt.CurrentWitnessStepPrefixNormal
import InitECandidate.Solver.Mpt.WitnessResolveSuffixNormal
import InitECandidate.Solver.Mpt.WitnessResolveFrame

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual unchanged resolver returns empty, a fresh physical hashed
node, or a bounded next slice from its real Patricia database. Its parser,
lookup and allocation share the same current state and physical frame. -/
theorem resolve_body_normal (data : CurrentTable.NodeBuild.Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64)
    (database : CurrentTable.NodeLookup.Database source data)
    (tableBefore : (CurrentTable.New.endPointer data.table data.cap).toNat≤heap.toNat)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word data.table)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (physical : Rlp.Validation.Arena source cursor limit)
    (small : length.toNat≤1024) (inputLower : 2701131776≤pointer.toNat) (before : pointer.toNat+length.toNat≤data.table.toNat)
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (Mpt.WitnessStep.body .resolve)=(some (.returned value),post)) :
    Mpt.WitnessDecode.LiveFrame source post heap cursor limit ∧ Rlp.Validation.Arena post cursor limit ∧ ResolveResult post data.table heap value := by
  have fits : pointer.toNat+length.toNat<2^64:=before.trans_lt data.table.isLt
  obtain ⟨ready,inner,answer,parsed,readyLive,prefixFrame,above,itemCell,nextDb,nextPointer,nextLength,forward,price,continued,endpoint⟩:=
    Mpt.CurrentWitnessStep.parsed_suffix_normal .resolve source post data.table pointer length dbCell pointerCell lengthCell live fits value normal
  have globals:=congrArg PanSemStateFiniteExact.globals prefixFrame.metadata
  change ready.globals=source.globals at globals
  have domain:=MemoryMetadata.domain prefixFrame.metadata
  have endian:=MemoryMetadata.endian prefixFrame.metadata
  have readyPhysical:=physical.of_fields source ready cursor limit domain globals
  have nextHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
  have earlier : ∀ query : BitVec 64,query.toNat<heap.toNat → ready.memory query=source.memory query:=
    fun query lower=>prefixFrame.outside query (Or.inl (by omega))
  have first:=Mpt.WitnessDecode.LiveFrame.of_parser source ready heap cursor limit live physical heapCell heapArena heapBound aligned
    prefixFrame.metadata earlier (above cursor limit physical)
  have currentDatabase:=database.of_before heap.toNat tableBefore domain endian earlier
  obtain ⟨header,payload,flag,answerEq,headerSmall,positive,extent,binary,listHeader⟩:=parsed
  rw [answerEq] at itemCell
  have classified:=Mpt.WitnessResolve.suffix_normal data ready inner pointer length header payload flag heap
    currentDatabase nextDb nextPointer nextLength itemCell nextHeap heapArena aligned small inputLower before readyLive.code value continued
  have finalPure : LocalEffects.erase post=LocalEffects.erase inner:=by rw [endpoint]; rfl
  have lift (frame : Mpt.WitnessDecode.LiveFrame ready inner heap cursor limit) : Mpt.WitnessDecode.LiveFrame source post heap cursor limit:=
    Mpt.WitnessDecode.LiveFrame.of_erase source inner source post heap cursor limit
      (Mpt.WitnessDecode.LiveFrame.compose source ready inner heap cursor heap cursor limit first frame (Nat.le_refl _) (Nat.le_refl _)) rfl finalPure
  have liftArena (arena : Rlp.Validation.Arena inner cursor limit) : Rlp.Validation.Arena post cursor limit:=by
    have finalDomain:=congrArg PanSemStateFiniteExact.memaddrs finalPure
    have finalGlobals:=congrArg PanSemStateFiniteExact.globals finalPure
    exact arena.of_fields inner post cursor limit finalDomain finalGlobals
  have readonly (pure : LocalEffects.erase inner=LocalEffects.erase ready) :
      Mpt.WitnessDecode.LiveFrame source post heap cursor limit ∧ Rlp.Validation.Arena post cursor limit := by
    have memory:=LocalEffects.memory_of_erase ready inner pure
    have suffix:=Mpt.WitnessDecode.LiveFrame.of_parser ready inner heap cursor limit readyLive readyPhysical nextHeap heapArena heapBound aligned
      (MemoryMetadata.of_frame pure) (fun query earlier=>congrFun memory query) (fun query above=>congrFun memory query)
    have suffixDomain:=congrArg PanSemStateFiniteExact.memaddrs pure
    have suffixGlobals:=congrArg PanSemStateFiniteExact.globals pure
    exact ⟨lift suffix,liftArena (readyPhysical.of_fields ready inner cursor limit suffixDomain suffixGlobals)⟩
  have hash_span (thirtyTwo : payload=32#64) :
      2701131776≤(pointer+header).toNat ∧ (pointer+header).toNat+32≤data.table.toNat := by
    have number : (pointer+header).toNat=pointer.toNat+header.toNat:=BitVec.toNat_add_of_lt (by omega)
    rw [thirtyTwo] at extent
    change header.toNat+32≤length.toNat at extent
    rw [number]
    omega
  rcases classified with ⟨valueEq,pure⟩|⟨valueEq,thirtyTwo,room,nodeArena,pure⟩|⟨nextPointer,nextLength,pending,valueEq,nextSmall,nextLower,nextBefore,pendingEq,pure⟩
  · obtain ⟨frame,named⟩:=readonly pure
    exact ⟨frame,named,Or.inl valueEq⟩
  · obtain ⟨suffix,named⟩:=Mpt.WitnessResolve.hash_live_frame ready inner heap (pointer+header) cursor limit nodeArena room aligned readyLive readyPhysical pure
    have memory:=LocalEffects.memory_of_erase (Mpt.WitnessResolve.hashAllocated ready heap (pointer+header)) post (finalPure.trans pure)
    have tag : post.memory heap=.word 0#64:=by
      rw [memory]
      exact Mpt.WitnessResolve.hash_allocated_tag ready heap (pointer+header)
    have hashCell : post.memory (heap+24#64)=.word (pointer+header):=by
      rw [memory]
      exact Mpt.WitnessResolve.hash_allocated_hash ready heap (pointer+header)
    have finalGlobals:=congrArg PanSemStateFiniteExact.globals (finalPure.trans pure)
    change post.globals=(Mpt.WitnessResolve.hashAllocated ready heap (pointer+header)).globals at finalGlobals
    obtain ⟨finalCell,finalArena,finalAligned,grows,bounded⟩:=Mpt.WitnessResolve.hash_allocated_heap ready heap (pointer+header) nodeArena room
    have actualCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 32#64))):=by
      rw [finalGlobals]
      exact finalCell
    exact ⟨lift suffix,liftArena named,
      Or.inr (Or.inl ⟨valueEq,nodeArena,room,tag,⟨pointer+header,(hash_span thirtyTwo).1,(hash_span thirtyTwo).2,hashCell⟩,
        _,actualCell,finalArena,finalAligned,grows,bounded⟩)⟩
  · obtain ⟨frame,named⟩:=readonly pure
    have pendingSpan : pending=0#64 ∨ 2701131776≤pending.toNat ∧ pending.toNat+32≤data.table.toNat:=by
      rcases pendingEq with zero|⟨same,thirtyTwo⟩
      · exact Or.inl zero
      · rw [same]
        exact Or.inr (hash_span thirtyTwo)
    exact ⟨frame,named,Or.inr (Or.inr ⟨nextPointer,nextLength,pending,valueEq,nextSmall,nextLower,nextBefore,pendingSpan⟩)⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.resolve_body_normal
