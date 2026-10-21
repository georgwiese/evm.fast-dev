import InitECandidate.Solver.Mpt.WitnessCoreStackBranchNext
import InitECandidate.Solver.Mpt.WitnessCoreStackBranchLast
import InitECandidate.Solver.Mpt.WitnessCoreBranchScope
import InitECandidate.Solver.Mpt.WitnessCoreResolveResultNode

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Physical outcomes of the complete branch-return path, after br/i
are restored. An advancing frame retains its actual allocation and
pending hash; a popped frame delivers an owned result to its parent. -/
def BranchStep (post : PanSemStateFiniteExact 64 Guest.HostMemory) (db heap cursor limit child oldSlot : BitVec 64)
    (entry : Entry) (rest : List Entry) : Prop:=
  (∃ nextEntry : Entry,
    nextEntry.record=entry.record ∧ nextEntry.mark=entry.mark ∧ nextEntry.pending=entry.pending ∧
    nextEntry.data.array=entry.data.array ∧ nextEntry.data.payload.startAddress=entry.data.payload.startAddress ∧
    View post db cursor.toNat heap.toNat (nextEntry::rest) ∧
    post.locals.lookup (ofString "top")=some (.val (.word nextEntry.record)) ∧
    post.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 nextEntry.data.payload.slotIndex))) ∧
    post.locals.lookup (ofString "mode")=some (.val (.word 2#64)) ∧
    post.locals.lookup (ofString "result")=some (.val (.word child)) ∧
    WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames (nextEntry::rest)) .resolve true<
      WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames (entry::rest)) .returning true) ∨
  (View post db cursor.toNat heap.toNat rest ∧ ∃ node,
    ResultOwned post (max (resultLower rest) entry.data.payload.startAddress) heap.toNat node ∧
    post.locals.lookup (ofString "top")=some (.val (.word (top rest))) ∧
    post.locals.lookup (ofString "result")=some (.val (.word node)) ∧
    post.locals.lookup (ofString "mode")=some (.val (.word 0#64)) ∧
    post.locals.lookup (ofString "slot")=some (.val (.word oldSlot)) ∧
    WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames rest) .returning true<
      WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames (entry::rest)) .returning true)

theorem return_branch_stack_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap cursor limit node child oldSlot : BitVec 64) (entry : Entry) (rest : List Entry)
    (index : Fin 16) (occupied : Fin 17)
    (view : View source db cursor.toNat heap.toNat (entry::rest)) (payload : entry.data.payload=.branch node index occupied)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word entry.record)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word oldSlot)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word 0#64)))
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source returnBranchNode=(none,post)) :
    BranchStep post db heap cursor limit child oldSlot entry rest ∧ post.globals=source.globals ∧
      Rlp.Validation.Arena post cursor limit ∧
      (∀ name : String,ofString "br"≠ofString name→ ofString "i"≠ofString name→ ofString "arr2"≠ofString name→
        ofString "bv"≠ofString name→ ofString "occ"≠ofString name→ ofString "top"≠ofString name→
        ofString "result"≠ofString name→ ofString "slot"≠ofString name→ ofString "mode"≠ofString name→
        post.locals.lookup (ofString name)=source.locals.lookup (ofString name)) ∧
      post.memaddrs=source.memaddrs ∧ post.be=source.be ∧ post.code=source.code ∧
      (∀ query : BitVec 64,entry.record.toNat+88≤query.toNat→ query.toNat<entry.data.payload.startAddress→ post.memory query=source.memory query) := by
  have head:=view.records entry List.mem_cons_self
  have used : occupied.val≤index.val:=by simpa only [CounterBound,payload] using view.counters entry List.mem_cons_self
  obtain ⟨inner,continued,postEq⟩:=return_branch_node_trace source post entry.record db node entry.data index occupied head payload topCell none normal
  let branchReady:=QueryBranch.bind source "br" node
  let ready:=QueryBranch.bind branchReady "i" (BitVec.ofNat 64 index.val)
  have readyView:=view.of_fields source ready db cursor.toNat heap.toNat (entry::rest) rfl rfl
  have readyArena : Rlp.Validation.Arena ready cursor limit:=
    ⟨arena.domain,arena.cursorGlobal,arena.limitGlobal,arena.ordered,arena.aligned,arena.lower,arena.upper⟩
  have fields:=branch_scope_entry_fields source entry.record node child index topCell resultCell
  have readyOther (name : String) (notBranch : ofString "br"≠ofString name) (notIndex : ofString "i"≠ofString name) :
      ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    (bind_lookup_other branchReady "i" name _ notIndex).trans (bind_lookup_other source "br" name node notBranch)
  have postOther (name : String) (notBranch : ofString "br"≠ofString name) (notIndex : ofString "i"≠ofString name) :
      post.locals.lookup (ofString name)=inner.locals.lookup (ofString name):=by
    rw [postEq,Input.ScalarScope.restore_other _ _ "br" name notBranch,Input.ScalarScope.restore_other _ _ "i" name notIndex]
  have memory : post.memory=inner.memory:=by rw [postEq]; rfl
  have domain : post.memaddrs=inner.memaddrs:=by rw [postEq]; rfl
  have globalEq : post.globals=inner.globals:=by rw [postEq]; rfl
  by_cases inside : index.val+1<16
  · obtain ⟨run,nextView,nextTop,nextSlot,nextMode,globals,other,band,innerDomain,endian,code,rank⟩:=branch_children_next_stack ready db heap cursor limit node child oldSlot 0#64 entry rest index occupied used inside
      readyView payload fields.1 fields.2.1 fields.2.2.1 fields.2.2.2 ((readyOther "slot" (by decide) (by decide)).trans slotCell)
      ((readyOther "mode" (by decide) (by decide)).trans modeCell)
    let nextIndex : Fin 16:=⟨index.val+1,inside⟩
    let nextEntry:={entry with data:={entry.data with payload:=.branch node nextIndex (occupiedNext index occupied used child)}}
    have innerEq : inner=advanced (branchCounterEntry ready entry.record node child index occupied) entry.record nextIndex:=
      (congrArg Prod.snd (continued.symm.trans run))
    rw [←innerEq] at nextView nextTop nextSlot nextMode globals other band innerDomain endian code
    have actualView:=nextView.of_fields inner post db cursor.toNat heap.toNat (nextEntry::rest) memory domain
    have step : BranchStep post db heap cursor limit child oldSlot entry rest:=Or.inl ⟨nextEntry,rfl,rfl,rfl,rfl,
      by simp only [nextEntry,payload,WitnessRecord.Payload.startAddress],actualView,
      (postOther "top" (by decide) (by decide)).trans nextTop,
      (postOther "slot" (by decide) (by decide)).trans nextSlot,
      (postOther "mode" (by decide) (by decide)).trans nextMode,
      (postOther "result" (by decide) (by decide)).trans ((other "result" (by decide) (by decide) (by decide)).trans fields.2.2.2),rank⟩
    have globalsPost : post.globals=source.globals:=globalEq.trans globals
    have scratch : Rlp.Validation.Arena post cursor limit:=
      ⟨by rw [domain,innerEq]; unfold advanced branchCounterEntry occupancyState; split <;> exact arena.domain,by rw [globalsPost]; exact arena.cursorGlobal,
        by rw [globalsPost]; exact arena.limitGlobal,arena.ordered,arena.aligned,arena.lower,arena.upper⟩
    refine ⟨step,globalsPost,scratch,?_,domain.trans innerDomain,?_,?_,?_⟩
    · intro name a b c d e f g h i
      exact (postOther name a b).trans ((other name b h i).trans (readyOther name a b))
    · rw [postEq]; exact endian
    · rw [postEq]; exact code
    · intro query first last
      rw [memory]
      exact band query first last
  · obtain ⟨tail,owned,actualTop,actualResult,globals,scratch,other,band,innerDomain,endian,code,rank⟩:=branch_children_last_stack_normal ready inner db heap cursor limit node child entry rest index occupied used inside
      readyView payload fields.1 fields.2.1 fields.2.2.1 fields.2.2.2 readyArena installed continued
    have actualView:=tail.of_fields inner post db cursor.toNat heap.toNat rest memory domain
    have actualOwned:=ResultOwned.of_fields inner post node (max (resultLower rest) entry.data.payload.startAddress) heap.toNat owned memory
    have actualMode : post.locals.lookup (ofString "mode")=some (.val (.word 0#64)):=
      (postOther "mode" (by decide) (by decide)).trans ((other "mode" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((readyOther "mode" (by decide) (by decide)).trans modeCell))
    have actualSlot : post.locals.lookup (ofString "slot")=some (.val (.word oldSlot)):=
      (postOther "slot" (by decide) (by decide)).trans ((other "slot" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((readyOther "slot" (by decide) (by decide)).trans slotCell))
    have step : BranchStep post db heap cursor limit child oldSlot entry rest:=Or.inr ⟨actualView,node,actualOwned,
      (postOther "top" (by decide) (by decide)).trans actualTop,
      (postOther "result" (by decide) (by decide)).trans actualResult,actualMode,actualSlot,rank⟩
    have globalsPost : post.globals=source.globals:=by
      apply HolFiniteMapExact.ext
      funext key
      rw [globalEq]
      exact globals key
    have scratchPost : Rlp.Validation.Arena post cursor limit:=
      ⟨by rw [domain]; exact scratch.domain,by rw [globalEq]; exact scratch.cursorGlobal,
        by rw [globalEq]; exact scratch.limitGlobal,scratch.ordered,scratch.aligned,scratch.lower,scratch.upper⟩
    refine ⟨step,globalsPost,scratchPost,?_,domain.trans innerDomain,?_,?_,?_⟩
    · intro name a b c d e f g h i
      exact (postOther name a b).trans ((other name b c d e f g).trans (readyOther name a b))
    · rw [postEq]; exact endian
    · rw [postEq]; exact code
    · intro query first last
      rw [memory]
      exact band query first last

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.return_branch_stack_normal
