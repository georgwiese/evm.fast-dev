import InitECandidate.Solver.Mpt.WitnessCoreRegistryBranchNext
import InitECandidate.Solver.Mpt.WitnessCoreRegistryBranchLast
import InitECandidate.Solver.Mpt.WitnessCoreRegistryCache
import InitECandidate.Solver.Mpt.WitnessCoreRegistryPayloadFrame

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def BranchRegistryResult (post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier : Nat)
    (db heap cursor : BitVec 64) (entry : Entry) (rest : List Entry) : Prop :=
  (∃ nextEntry : Entry,nextEntry.record=entry.record ∧ WitnessRecord.View post nextEntry.record db nextEntry.data ∧
    post.locals.lookup (ofString "mode")=some (.val (.word 2#64)) ∧
    Nonempty (ActiveRegistry post frontier db ⟨heap,cursor,nextEntry::rest,.resolve,true⟩)) ∨
  (post.locals.lookup (ofString "mode")=some (.val (.word 0#64)) ∧
    Nonempty (ActiveRegistry post frontier db ⟨heap,cursor,rest,.returning,true⟩))

/-- Whole original branch return, through both real br/i declarations,
genuine continuing/final child execution, and both scope restorations. -/
theorem ActiveRegistry.branch_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap cursor limit node child oldSlot : BitVec 64) (entry : Entry) (rest : List Entry)
    (index : Fin 16) (occupied : Fin 17)
    (registry : ActiveRegistry source frontier db ⟨heap,cursor,entry::rest,.returning,true⟩)
    (view : View source db cursor.toNat heap.toNat (entry::rest)) (payload : entry.data.payload=.branch node index occupied)
    (frontierLower : 2713731432≤frontier) (nodeFloor : frontier≤node.toNat) (dbUpper : db.toNat≤33806089496)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word entry.record)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word oldSlot)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word 0#64)))
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source returnBranchNode=(none,post)) :
    BranchRegistryResult post frontier db heap cursor entry rest := by
  have head:=view.records entry List.mem_cons_self
  have used : occupied.val≤index.val := by simpa only [CounterBound,payload] using view.counters entry List.mem_cons_self
  obtain ⟨inner,continued,postEq⟩:=return_branch_node_trace source post entry.record db node entry.data index occupied head payload topCell none normal
  let branchReady:=QueryBranch.bind source "br" node
  let ready:=QueryBranch.bind branchReady "i" (BitVec.ofNat 64 index.val)
  have readyView:=view.of_fields source ready db cursor.toNat heap.toNat (entry::rest) rfl rfl
  have readyArena : Rlp.Validation.Arena ready cursor limit := arena.of_fields source ready cursor limit rfl rfl
  have fields:=branch_scope_entry_fields source entry.record node child index topCell resultCell
  have readyOther (name : String) (notBranch : ofString "br"≠ofString name) (notIndex : ofString "i"≠ofString name) :
      ready.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    (bind_lookup_other branchReady "i" name _ notIndex).trans (bind_lookup_other source "br" name node notBranch)
  have postOther (name : String) (notBranch : ofString "br"≠ofString name) (notIndex : ofString "i"≠ofString name) :
      post.locals.lookup (ofString name)=inner.locals.lookup (ofString name) := by
    rw [postEq,Input.ScalarScope.restore_other _ _ "br" name notBranch,Input.ScalarScope.restore_other _ _ "i" name notIndex]
  have memory : post.memory=inner.memory := by rw [postEq]; rfl
  have domain : post.memaddrs=inner.memaddrs := by rw [postEq]; rfl
  obtain ⟨readyRegistry,readyValid⟩:=registry.of_fields source ready frontier db _ rfl rfl (readyOther "result" (by decide) (by decide))
  by_cases inside : index.val+1<16
  · obtain ⟨run,nextView,nextTop,nextSlot,nextMode,globals,other,band,innerDomain,endian,code,rank⟩:=branch_children_next_stack ready db heap cursor limit node child oldSlot 0#64 entry rest index occupied used inside
      readyView payload fields.1 fields.2.1 fields.2.2.1 fields.2.2.2 ((readyOther "slot" (by decide) (by decide)).trans slotCell)
      ((readyOther "mode" (by decide) (by decide)).trans modeCell)
    let nextIndex : Fin 16:=⟨index.val+1,inside⟩
    let nextEntry : Entry:={entry with data:={entry.data with payload:=.branch node nextIndex (occupiedNext index occupied used child)}}
    have innerEq : inner=advanced (branchCounterEntry ready entry.record node child index occupied) entry.record nextIndex := congrArg Prod.snd (continued.symm.trans run)
    rw [←innerEq] at nextView nextMode
    have richInner : Nonempty (ActiveRegistry inner frontier db ⟨heap,cursor,nextEntry::rest,.resolve,true⟩) := by
      rw [innerEq]
      exact readyRegistry.branch_advanced ready frontier db heap cursor node child entry rest index nextIndex occupied used rfl readyView payload frontierLower
        (readyRegistry.returned rfl child fields.2.2.2)
    obtain ⟨innerRegistry⟩:=richInner
    obtain ⟨postRegistry,postValid⟩:=innerRegistry.of_fields inner post frontier db _ memory domain (postOther "result" (by decide) (by decide))
    have actualView:=nextView.of_fields inner post db cursor.toNat heap.toNat (nextEntry::rest) memory domain
    exact Or.inl ⟨nextEntry,rfl,actualView.records nextEntry List.mem_cons_self,
      (postOther "mode" (by decide) (by decide)).trans nextMode,⟨postRegistry⟩⟩
  · obtain ⟨tail,owned,actualTop,actualResult,globals,scratch,other,band,innerDomain,endian,code,rank⟩:=branch_children_last_stack_normal ready inner db heap cursor limit node child entry rest index occupied used inside
      readyView payload fields.1 fields.2.1 fields.2.2.1 fields.2.2.2 readyArena installed continued
    obtain ⟨innerRegistry⟩:=readyRegistry.branch_last_normal ready inner frontier db heap cursor limit node child entry rest index occupied used inside
      readyView payload frontierLower nodeFloor dbUpper fields.1 fields.2.1 fields.2.2.1 fields.2.2.2 readyArena installed continued
    obtain ⟨postRegistry,postValid⟩:=innerRegistry.of_fields inner post frontier db _ memory domain (postOther "result" (by decide) (by decide))
    have actualMode : post.locals.lookup (ofString "mode")=some (.val (.word 0#64)) :=
      (postOther "mode" (by decide) (by decide)).trans ((other "mode" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((readyOther "mode" (by decide) (by decide)).trans modeCell))
    exact Or.inr ⟨actualMode,⟨postRegistry⟩⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.branch_normal
