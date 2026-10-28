import InitECandidate.Solver.Mpt.CurrentWitnessDecodeValueFrame
import InitECandidate.Solver.Mpt.CurrentCompactPersistentFrame
import InitECandidate.Solver.Mpt.CurrentWitnessDecodeZero
import InitECandidate.Solver.Mpt.CurrentWitnessTerminalResult
import InitECandidate.Solver.Input.SequenceChoice

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem current_after_compact_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer heap parentPointer parentLength nibbles nibbleLength leaf : BitVec 64)
    (bytes : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (selected : items[1]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word parentPointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word parentLength)))
    (compactCell : source.locals.lookup (ofString "cn")=some (.rStruct [.val (.word nibbles),.val (.word nibbleLength),.val (.word leaf)]))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterCompact=(some (.returned value),post)) :
    TerminalResult heap value ∧ PersistentNormalFrame source post heap := by
  have choice : evaluateHOLFiniteState source (.ite (.cmp .notEqual (field "cn" 2) (.const 0#64)) leafBody .skip)=
      if leaf≠0#64 then evaluateHOLFiniteState source leafBody else (none,source) := by
    by_cases nonzero : leaf≠0#64
    · simp [evaluateHOLFiniteState_ite,field,localVar,evalHOLExact,compactCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,nonzero]
    · have zero : leaf=0#64:=by simpa using nonzero
      simp [evaluateHOLFiniteState_ite,field,localVar,evalHOLExact,compactCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero,evaluateHOLFiniteState_skip]
  have actual:=sequence_choice source _ leafBody extensionBody (leaf≠0#64) choice leaf_body_no_fallthrough
  rw [after_compact_shape,actual] at normal
  by_cases nonzero : leaf≠0#64
  · rw [if_pos nonzero] at normal
    obtain ⟨valueEq,frame⟩:=current_leaf_body_frame source post array pointer heap parentPointer parentLength nibbles nibbleLength leaf bytes items item rows selected
      arrayCell pointerCell lengthCell compactCell heapCell heapArena heapBound aligned arena value normal
    exact ⟨⟨heap,valueEq,Or.inr ⟨Nat.le_refl _,heapBound⟩⟩,frame⟩
  · rw [if_neg nonzero] at normal
    exact (extension_body_no_return source post arena value normal).elim

/-- The actual compact allocation protects the physical second row and
passes its real advanced heap into the leaf path. -/
theorem current_compact_call_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer itemPointer header payload flag heap parentPointer parentLength : BitVec 64)
    (bytes : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (selected : items[1]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word parentPointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word parentLength)))
    (pathCell : source.locals.lookup (ofString "pi")=some (Rlp.Item.result itemPointer header payload flag))
    (payloadBound : payload.toNat≤bytes) (small : bytes≤1024) (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source compactCall=(some (.returned value),post)) : TerminalResult heap value ∧ PersistentNormalFrame source post heap := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [field "pi" 1,field "pi" 2]=
      some [.val (.word (itemPointer+header)),.val (.word (BitVec.ofNat 64 payload.toNat))] := by
    simp [field,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pathCell,Rlp.Item.result]
  rw [compact_shape] at normal
  obtain ⟨target,nibbles,leaf,inner,snapshot,continued,endpoint⟩:=CompactToNibbles.scoped_current_normal source post (itemPointer+header) heap payload.toNat
    (by omega) "cn" [field "pi" 1,field "pi" 2] afterCompact args heapCell heapArena heapBound aligned arena value normal
  let ready:=CallNormal.continuationEntry source target "cn" (CompactToNibbles.output heap nibbles leaf)
  let next:=PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*payload.toNat))
  have domain:=MemoryMetadata.domain snapshot.metadata
  change target.memaddrs=source.memaddrs at domain
  have currentRows : Rows ready array pointer bytes items := rows.earlier source ready array pointer bytes items heap.toNat beforeArray
    domain (fun query before=>snapshot.memory query (Or.inl before))
  have currentArray : ready.locals.lookup (ofString "arr")=some (.val (.word array)):=
    (CallNormal.continuation_lookup_other source target "cn" "arr" _ (by decide)).trans arrayCell
  have currentPointer : ready.locals.lookup (ofString "p")=some (.val (.word parentPointer)):=
    (CallNormal.continuation_lookup_other source target "cn" "p" _ (by decide)).trans pointerCell
  have currentLength : ready.locals.lookup (ofString "n")=some (.val (.word parentLength)):=
    (CallNormal.continuation_lookup_other source target "cn" "n" _ (by decide)).trans lengthCell
  have compactCell : ready.locals.lookup (ofString "cn")=some (CompactToNibbles.output heap nibbles leaf):=CallNormal.continuation_lookup_same _ _ _ _
  obtain ⟨nodeResult,tail⟩:=current_after_compact_frame ready inner array pointer next parentPointer parentLength heap (BitVec.ofNat 64 nibbles) leaf bytes items item
    currentRows selected currentArray currentPointer currentLength compactCell snapshot.heapCell snapshot.nextArena snapshot.nextBound snapshot.nextAligned
    (snapshot.arena.of_frame rfl) value continued
  have first : PersistentNormalFrame source ready heap:=snapshot.persistent_frame.of_erase source target source ready heap rfl rfl
  have grows : heap.toNat≤next.toNat:=by dsimp [next]; have grows:=snapshot.grows; omega
  have complete:=first.trans source ready inner heap next tail grows
  exact ⟨nodeResult.mono heap next grows,complete.of_erase source inner source post heap rfl (by rw [endpoint]; rfl)⟩

/-- Both item calls, the compact allocation and the genuine fresh leaf
retain the same entering heap/input frame on every actual normal pair return. -/
theorem current_pair_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer heap parentPointer parentLength : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (first second : Rlp.ListItem) (rows : Rows source array pointer bytes items)
    (firstSelected : items[0]?=some first) (secondSelected : items[1]?=some second)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word parentPointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word parentLength)))
    (small : bytes≤1024) (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source pairBody=(some (.returned value),post)) : TerminalResult heap value ∧ PersistentNormalFrame source post heap := by
  obtain ⟨args,positive,rowBound,lower,upper⟩:=rows.arguments source array pointer bytes 0 items first firstSelected arrayCell
  have fits : (Rlp.Slices.itemPointer pointer items 0).toNat+first.total.toNat<2^64:=by have h:=rows.fits; omega
  rw [path_shape] at normal
  obtain ⟨answer,clock,inner,valid,forward,price,continued,endpoint⟩:=Rlp.CurrentItem.scoped_normal source post
    (Rlp.Slices.itemPointer pointer items 0) first.total arena fits "pi" (recordArguments 0) afterPath args value normal
  obtain ⟨header,payload,flag,answerEq,headerBound,itemPositive,itemBound,binary,listHeader⟩:=valid
  rw [answerEq] at continued
  let ready:=setVarHOLFinite (ofString "pi") (Rlp.Item.result (Rlp.Slices.itemPointer pointer items 0) header payload flag) {source with clock:=clock}
  have currentRows : Rows ready array pointer bytes items:=rows.frame source ready array pointer bytes items rfl (by intros; rfl)
  have currentArray : ready.locals.lookup (ofString "arr")=some (.val (.word array)):=
    (CallNormal.continuation_lookup_other source {source with clock:=clock} "pi" "arr" _ (by decide)).trans arrayCell
  have currentPointer : ready.locals.lookup (ofString "p")=some (.val (.word parentPointer)):=
    (CallNormal.continuation_lookup_other source {source with clock:=clock} "pi" "p" _ (by decide)).trans pointerCell
  have currentLength : ready.locals.lookup (ofString "n")=some (.val (.word parentLength)):=
    (CallNormal.continuation_lookup_other source {source with clock:=clock} "pi" "n" _ (by decide)).trans lengthCell
  have pathCell : ready.locals.lookup (ofString "pi")=some (Rlp.Item.result (Rlp.Slices.itemPointer pointer items 0) header payload flag):=
    CallNormal.continuation_lookup_same source {source with clock:=clock} "pi" _
  have readyArena : CurrentStartup.ArenaState ready:=arena.of_frame rfl
  rw [after_path_shape] at continued
  have actual:=(Fail.guard_return ready inner (.cmp .notEqual (field "pi" 0) (.const 0#64)) [.const 5#64] compactCall value readyArena.code continued).2
  obtain ⟨nodeResult,frame⟩:=current_compact_call_frame ready inner array pointer (Rlp.Slices.itemPointer pointer items 0) header payload flag heap parentPointer parentLength
    bytes items second currentRows secondSelected currentArray currentPointer currentLength pathCell (by omega) small beforeArray heapCell heapArena heapBound aligned readyArena value actual
  exact ⟨nodeResult,frame.of_erase ready inner source post heap rfl (by rw [endpoint]; rfl)⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_after_compact_frame
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_compact_call_frame
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_pair_frame
