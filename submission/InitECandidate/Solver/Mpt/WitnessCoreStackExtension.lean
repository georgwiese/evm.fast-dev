import InitECandidate.Solver.Mpt.WitnessCoreStackReturnFrame
import InitECandidate.Solver.Mpt.WitnessCoreExtensionFrame
import InitECandidate.Solver.Mpt.WitnessCoreResultNode

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem extension_finished_other (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap nibbles length child previous kind : BitVec 64) (data : WitnessRecord.Description) (name : String)
    (notKind : ofString "ck"≠ofString name) (notNode : ofString "ex"≠ofString name)
    (notTop : ofString "top"≠ofString name) (notResult : ofString "result"≠ofString name) :
    (extensionFinishedState source heap nibbles length child previous kind data).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  unfold extensionFinishedState
  rw [Input.ScalarScope.restore_other _ _ "ck" name notKind,Input.ScalarScope.restore_other _ _ "ex" name notNode]
  exact (bind_lookup_other _ "result" name heap notResult).trans ((bind_lookup_other _ "top" name previous notTop).trans
    ((bind_lookup_other _ "ex" name heap notNode).trans (bind_lookup_other source "ck" name kind notKind)))

namespace Stack

/-- A genuine extension return derives its nonnull supported child,
allocates the original56-byte node, and pops the actual physical stack.
The fresh result follows the waiting parent's allocation frontier. -/
theorem return_extension_stack_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap cursor limit nibbles length child : BitVec 64) (entry : Entry) (rest : List Entry)
    (view : View source db cursor.toNat heap.toNat (entry::rest)) (payload : entry.data.payload=.extension nibbles length)
    (owned : ResultOwned source entry.mark heap.toNat child)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word entry.record)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source returnExtension=(none,post)) :
    ∃ nextHeap,
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧
      AllocatedBytes.Arena nextHeap 0 ∧ nextHeap.toNat%8=0 ∧ heap.toNat≤nextHeap.toNat ∧
      Rlp.Validation.Arena post cursor limit ∧ View post db cursor.toNat nextHeap.toNat rest ∧
      ResultOwned post (resultLower rest) nextHeap.toNat heap ∧
      post.locals.lookup (ofString "top")=some (.val (.word (top rest))) ∧
      post.locals.lookup (ofString "result")=some (.val (.word heap)) ∧
      (∀ key,key≠ofString "heap_ptr"→ post.globals.lookup key=source.globals.lookup key) ∧
      (∀ name : String,ofString "ck"≠ofString name→ ofString "ex"≠ofString name→ ofString "top"≠ofString name→
        ofString "result"≠ofString name→ post.locals.lookup (ofString name)=source.locals.lookup (ofString name)) ∧
      (∀ query : BitVec 64,cursor.toNat≤query.toNat→ query.toNat<heap.toNat→ post.memory query=source.memory query) ∧
      WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames rest) .returning true<
        WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames (entry::rest)) .returning true := by
  have head:=view.records entry List.mem_cons_self
  have mark:=view.marks entry List.mem_cons_self
  have before:=(view.before entry List.mem_cons_self).mono entry.data entry.mark heap.toNat mark
  have heapLower : 2713731432≤heap.toNat:=by have lower:=head.arrayFloor; have upper:=before.1; omega
  have nonzero : child≠0#64:=by
    have split:=normal
    rw [return_extension_shape] at split
    obtain ⟨guardPost,guardRun,kindRun⟩:=Input.sequence_none source post _ extensionKindRead split
    obtain ⟨passed,same⟩:=Fail.guard_normal source guardPost (.cmp .equal (localVar "result") (.const 0#64)) [.const 8#64] installed guardRun
    intro zero
    have one : eval source (.cmp .equal (localVar "result") (.const 0#64))=some (.val (.word 1#64)):=by
      simp [eval,evalHOLExact,localVar,toExact,resultCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have impossible : (1#64 : BitVec 64)=0#64:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using one.symm.trans passed
    exact (by decide : (1#64 : BitVec 64)≠0#64) impossible
  have childOwned : ResultNode source entry.mark heap.toNat child:=owned.resolve_left nonzero
  obtain ⟨kind,kindCell,kindBound⟩:=childOwned.kind
  have childMapped : source.memaddrs child:=by
    simpa only [byteAddress,BitVec.add_zero] using
      AllocatedBytes.word_mapped source child 32 0 head.rows.domain childOwned.arena (by decide) childOwned.aligned (by decide)
  obtain ⟨nonnull,supported,nodeArena,funded,postEq⟩:=return_extension_normal source post entry.record db heap nibbles length child (top rest) kind entry.data
    head payload topCell resultCell view.links.1 childMapped kindCell heapCell heapArena heapAligned heapLower before installed normal
  have frame : WitnessDecode.NormalFrame source post heap cursor limit:=by
    rw [postEq]
    exact extension_finished_frame source heap cursor limit nibbles length child (top rest) kind entry.data nodeArena heapAligned arena
  obtain ⟨nextHeap,nextCell,nextArena,nextAligned,grows⟩:=frame.nextHeap
  have scratchCell : post.globals.lookup (ofString "scratch_ptr")=source.globals.lookup (ofString "scratch_ptr"):=by
    rw [postEq]
    change (PersistentAlloc.post source heap 56#64).globals.lookup (ofString "scratch_ptr")=_
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,show ofString "heap_ptr"≠ofString "scratch_ptr" from by decide]
  have scratch : Rlp.Validation.Arena post cursor limit:=
    ⟨by rw [frame.domain]; exact arena.domain,
      scratchCell.trans arena.cursorGlobal,
      (frame.globals _ (by decide) (by decide)).trans arena.limitGlobal,
      arena.ordered,arena.aligned,arena.lower,arena.upper⟩
  have oldStack:=view.frame source post db cursor.toNat heap.toNat cursor.toNat nextHeap.toNat (entry::rest)
    heapLower (Nat.le_refl _) grows frame.domain frame.memory
  have parentLower : resultLower rest≤heap.toNat:=
    (view.tail source db cursor.toNat heap.toNat entry rest).result_lower_le_heap source db cursor.toNat heap.toNat rest heapLower
  have nodeBefore : heap.toNat+56≤nextHeap.toNat:=by
    have checked:=PersistentAlloc.guards heap 56#64 nodeArena.upper
    have roundedCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 56#64))):=by
      rw [postEq]
      change (PersistentAlloc.post source heap 56#64).globals.lookup (ofString "heap_ptr")=_
      simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
    have same : nextHeap=PersistentAlloc.rounded heap 56#64:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (nextCell.symm.trans roundedCell)))
    rw [same]
    exact checked.2.2.1
  have postTag : post.memory heap=.word 2#64:=by rw [postEq]; exact extension_finished_tag source heap nibbles length child (top rest) kind entry.data
  have resultOwned : ResultOwned post (resultLower rest) nextHeap.toNat heap:=
    Or.inr (ResultNode.of_region post heap 2#64 56 (resultLower rest) nextHeap.toNat nodeArena (by decide) heapAligned parentLower nodeBefore postTag (by decide))
  have fields:=extension_finished_fields source heap nibbles length child (top rest) kind entry.data
  have actualTop : post.locals.lookup (ofString "top")=some (.val (.word (top rest))):=by rw [postEq]; exact fields.1
  have actualResult : post.locals.lookup (ofString "result")=some (.val (.word heap)):=by rw [postEq]; exact fields.2
  have other (key) (notHeap : key≠ofString "heap_ptr") : post.globals.lookup key=source.globals.lookup key:=by
    rw [postEq]
    change (PersistentAlloc.post source heap 56#64).globals.lookup key=source.globals.lookup key
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm notHeap]
  have locals (name : String) (a : ofString "ck"≠ofString name) (b : ofString "ex"≠ofString name)
      (c : ofString "top"≠ofString name) (d : ofString "result"≠ofString name) : post.locals.lookup (ofString name)=source.locals.lookup (ofString name):=by
    rw [postEq]
    exact extension_finished_other source heap nibbles length child (top rest) kind entry.data name a b c d
  have rank : WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames rest) .returning true<
      WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames (entry::rest)) .returning true:=by
    simpa only [frames,List.map_cons] using WitnessStackRank.pop (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames rest) entry.data.payload.frame
  exact ⟨nextHeap,nextCell,nextArena,nextAligned,grows,scratch,oldStack.tail post db cursor.toNat nextHeap.toNat entry rest,
    resultOwned,actualTop,actualResult,other,locals,frame.memory,rank⟩

end Stack
end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.extension_finished_other
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.return_extension_stack_normal
