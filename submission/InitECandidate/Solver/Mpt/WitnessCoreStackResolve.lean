import InitECandidate.Solver.Mpt.WitnessCoreStackHash
import InitECandidate.Solver.Mpt.WitnessCoreResolveResultNode
import InitECandidate.Solver.Input.CoreResolveNormal
import InitECandidate.Solver.Mpt.WitnessCoreResolveScope

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def ResolveStep (post : PanSemStateFiniteExact 64 Guest.HostMemory) (db heap cursor limit : BitVec 64)
    (entry : Entry) (rest : List Entry) : Prop:=
  ∃ next pending,
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) ∧
    AllocatedBytes.Arena next 0 ∧ next.toNat%8=0 ∧ heap.toNat≤next.toNat ∧ Rlp.Validation.Arena post cursor limit ∧
    View post db cursor.toNat next.toNat ({entry with pending:=some pending}::rest) ∧
    post.locals.lookup (ofString "top")=some (.val (.word entry.record)) ∧
    post.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 entry.data.payload.slotIndex))) ∧
    ((pending=0#64 ∧ ∃ node,
        post.locals.lookup (ofString "result")=some (.val (.word node)) ∧
        post.locals.lookup (ofString "mode")=some (.val (.word 0#64)) ∧ ResultOwned post heap.toNat next.toNat node ∧
        WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames ({entry with pending:=some pending}::rest)) .returning true<
          WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames (entry::rest)) .resolve true) ∨
      ∃ pointer length,
        post.locals.lookup (ofString "cur_p")=some (.val (.word pointer)) ∧
        post.locals.lookup (ofString "cur_n")=some (.val (.word length)) ∧
        post.locals.lookup (ofString "mode")=some (.val (.word 1#64)) ∧
        length.toNat≤1024 ∧ 2713731432≤pointer.toNat ∧ pointer.toNat+length.toNat≤db.toNat ∧ HashValid db pending ∧
        WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames ({entry with pending:=some pending}::rest)) .decode true<
          WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames (entry::rest)) .resolve true)

end InitECandidate.Solver.Mpt.WitnessCore.Stack

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Mpt.WitnessCore Mpt.WitnessCore.Stack

/-- Whole unchanged resolver mode preserves the actual older stack,
installs its genuine pending hash and moves to returning or bounded
decode input. Its true callee/frame/result and both actual caller scopes
derive every next-state fact and the strict physical rank decrease. -/
theorem core_resolve_stack_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap cursor limit oldResult oldPointer oldLength oldMode : BitVec 64)
    (entry : Mpt.WitnessCore.Stack.Entry) (rest : List Mpt.WitnessCore.Stack.Entry)
    (view : View source db cursor.toNat heap.toNat (entry::rest)) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word entry.record)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 entry.data.payload.slotIndex))))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word oldResult)))
    (pointerCell : source.locals.lookup (ofString "cur_p")=some (.val (.word oldPointer)))
    (lengthCell : source.locals.lookup (ofString "cur_n")=some (.val (.word oldLength)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word oldMode)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapAligned : heap.toNat%8=0) (arena : Rlp.Validation.Arena source cursor limit)
    (below : cursor.toNat≤2713717616) (heapLower : 2713731432≤heap.toNat)
    (installed : OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source resolveBranch=(none,post)) :
    ResolveStep post db heap cursor limit entry rest ∧
      post.locals.lookup (ofString "db")=source.locals.lookup (ofString "db") ∧
      post.locals.lookup (ofString "go")=source.locals.lookup (ofString "go") := by
  have headView:=view.records entry List.mem_cons_self
  have headBefore:=(view.before entry List.mem_cons_self).mono entry.data entry.mark heap.toNat (view.marks entry List.mem_cons_self)
  have headAbove:=view.above entry List.mem_cons_self
  obtain ⟨built,returned,frame,result,postRecord,scratch,postGlobals,shape⟩:=core_resolve_normal input source post
    entry.record db heap cursor limit oldResult oldPointer oldLength oldMode entry.data headView boundary dbCell topCell slotCell resultCell pointerCell lengthCell modeCell
    heapCell arena below headAbove heapLower headBefore installed normal
  let arrState:=QueryBranch.bind source "arr" entry.data.array
  let ready:=CallNormal.continuationEntry arrState built "r" returned
  obtain ⟨next,nextCell,nextArena,aligned,grows⟩:=frame.nextHeap
  have readyView:=view.frame source ready db cursor.toNat heap.toNat cursor.toNat next.toNat (entry::rest) heapLower (Nat.le_refl _) grows frame.domain frame.memory
  have nextLower : 2713731432≤next.toNat:=heapLower.trans grows
  have actualNext : post.globals.lookup (ofString "heap_ptr")=some (.val (.word next)):=by rw [postGlobals]; exact nextCell
  have readyOther (name : String) (notArr : ofString "arr"≠ofString name) (notR : ofString "r"≠ofString name) :
      ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    (CallNormal.continuation_lookup_other arrState built "r" name returned notR).trans
      (bind_lookup_other source "arr" name entry.data.array notArr)
  rcases shape with ⟨node,valueEq,nodeChoice,postEq⟩|⟨pointer,length,pending,valueEq,small,lower,upper,hashSpan,postEq⟩
  · have hashView:=set_pending ready db 0#64 cursor.toNat next.toNat entry rest readyView nextLower (Or.inl rfl)
    have postMemory : post.memory=(hashState ready entry.record 0#64).memory:=by rw [postEq]; rfl
    have postDomain : post.memaddrs=(hashState ready entry.record 0#64).memaddrs:=by rw [postEq]; rfl
    have postView:=hashView.of_fields _ post db cursor.toNat next.toNat _ postMemory postDomain
    rw [valueEq] at result
    have owned:=resolve_result_owned ready db heap next node heapAligned result nextCell
    have recordUpper:=headView.ceiling
    have number : (entry.record+80#64).toNat=entry.record.toNat+80:=byteAddress_toNat entry.record 80 (by omega)
    have hashedOwned:=owned.store_below ready node (entry.record+80#64) 0#64 heap.toNat next.toNat (by omega)
    have postOwned:=hashedOwned.of_fields _ post node heap.toNat next.toNat postMemory
    have fields:=resolve_scoped_terminal_fields source ready entry.data.array entry.record node
    have actualResult : post.locals.lookup (ofString "result")=some (.val (.word node)):=by rw [postEq]; exact fields.1
    have actualMode : post.locals.lookup (ofString "mode")=some (.val (.word 0#64)):=by rw [postEq]; exact fields.2.1
    have preserved (name : String) (notArr : ofString "arr"≠ofString name) (notR : ofString "r"≠ofString name)
        (notResult : ofString "result"≠ofString name) (notMode : ofString "mode"≠ofString name) : post.locals.lookup (ofString name)=source.locals.lookup (ofString name):=by
      rw [postEq]
      exact (resolve_scoped_terminal_other source ready entry.data.array entry.record node name notArr notR notResult notMode).trans (readyOther name notArr notR)
    have actualTop : post.locals.lookup (ofString "top")=some (.val (.word entry.record)):=
      (preserved "top" (by decide) (by decide) (by decide) (by decide)).trans topCell
    have actualSlot : post.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 entry.data.payload.slotIndex))):=
      (preserved "slot" (by decide) (by decide) (by decide) (by decide)).trans slotCell
    have rank : Mpt.WitnessStackRank.rank (Mpt.WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames ({entry with pending:=some 0#64}::rest)) .returning true<
        Mpt.WitnessStackRank.rank (Mpt.WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames (entry::rest)) .resolve true:=
      lt_trans (Mpt.WitnessStackRank.terminal _ _) (Mpt.WitnessStackRank.resolve_decode _ _)
    exact ⟨⟨next,0#64,actualNext,nextArena,aligned,grows,scratch,postView,actualTop,actualSlot,
      Or.inl ⟨rfl,node,actualResult,actualMode,postOwned,rank⟩⟩,
      preserved "db" (by decide) (by decide) (by decide) (by decide),preserved "go" (by decide) (by decide) (by decide) (by decide)⟩
  · have valid : HashValid db pending:=hashSpan
    have hashView:=set_pending ready db pending cursor.toNat next.toNat entry rest readyView nextLower valid
    have postMemory : post.memory=(hashState ready entry.record pending).memory:=by rw [postEq]; rfl
    have postDomain : post.memaddrs=(hashState ready entry.record pending).memaddrs:=by rw [postEq]; rfl
    have postView:=hashView.of_fields _ post db cursor.toNat next.toNat _ postMemory postDomain
    have fields:=resolve_scoped_decode_fields source ready entry.data.array entry.record pointer length pending
    have actualPointer : post.locals.lookup (ofString "cur_p")=some (.val (.word pointer)):=by rw [postEq]; exact fields.1
    have actualLength : post.locals.lookup (ofString "cur_n")=some (.val (.word length)):=by rw [postEq]; exact fields.2.1
    have actualMode : post.locals.lookup (ofString "mode")=some (.val (.word 1#64)):=by rw [postEq]; exact fields.2.2.1
    have preserved (name : String) (notArr : ofString "arr"≠ofString name) (notR : ofString "r"≠ofString name)
        (notPointer : ofString "cur_p"≠ofString name) (notLength : ofString "cur_n"≠ofString name) (notMode : ofString "mode"≠ofString name) : post.locals.lookup (ofString name)=source.locals.lookup (ofString name):=by
      rw [postEq]
      exact (resolve_scoped_decode_other source ready entry.data.array entry.record pointer length pending name notArr notR notPointer notLength notMode).trans (readyOther name notArr notR)
    have actualTop : post.locals.lookup (ofString "top")=some (.val (.word entry.record)):=
      (preserved "top" (by decide) (by decide) (by decide) (by decide) (by decide)).trans topCell
    have actualSlot : post.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 entry.data.payload.slotIndex))):=
      (preserved "slot" (by decide) (by decide) (by decide) (by decide) (by decide)).trans slotCell
    exact ⟨⟨next,pending,actualNext,nextArena,aligned,grows,scratch,postView,actualTop,actualSlot,
      Or.inr ⟨pointer,length,actualPointer,actualLength,actualMode,small,lower,upper,valid,Mpt.WitnessStackRank.resolve_decode _ _⟩⟩,
      preserved "db" (by decide) (by decide) (by decide) (by decide) (by decide),
      preserved "go" (by decide) (by decide) (by decide) (by decide) (by decide)⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.core_resolve_stack_normal
