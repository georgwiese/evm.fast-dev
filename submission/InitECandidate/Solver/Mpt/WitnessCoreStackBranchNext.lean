import InitECandidate.Solver.Mpt.WitnessCoreStackReturnFrame
import InitECandidate.Solver.Mpt.WitnessCoreBranchNext
import InitECandidate.Solver.Mpt.WitnessCoreResolveRows

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem branch_next_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record node child : BitVec 64)
    (index : Fin 16) (occupied : Fin 17) (nextIndex : Fin 16) (query : BitVec 64)
    (notChild : query≠WitnessRecord.childAddress node index) (notOccupied : query≠record+40#64) (notIndex : query≠record+32#64) :
    (advanced (branchCounterEntry source record node child index occupied) record nextIndex).memory query=source.memory query := by
  change StoreWord.put (branchCounterEntry source record node child index occupied).memory (record+32#64) (BitVec.ofNat 64 nextIndex.val) query=source.memory query
  rw [StoreWord.put,if_neg notIndex]
  exact branch_counter_entry_memory source record node child index occupied query notChild notOccupied

end InitECandidate.Solver.Mpt.WitnessCore

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual continuing-child branch updates only its own node and
record. Every older activation remains physically owned; PREV and HASH
survive, counters remain bounded, and the real next resolver slot/mode
and pending-frame rank are derived from the unchanged program. -/
theorem branch_children_next_stack (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap cursor limit node child oldSlot oldMode : BitVec 64) (entry : Entry) (rest : List Entry)
    (index : Fin 16) (occupied : Fin 17) (used : occupied.val≤index.val) (inside : index.val+1<16)
    (view : View source db cursor.toNat heap.toNat (entry::rest)) (payload : entry.data.payload=.branch node index occupied)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word entry.record)))
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word node)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index.val))))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word oldSlot)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word oldMode))) :
    let nextIndex : Fin 16:=⟨index.val+1,inside⟩
    let nextOccupied:=occupiedNext index occupied used child
    let nextEntry:={entry with data:={entry.data with payload:=.branch node nextIndex nextOccupied}}
    let next:=advanced (branchCounterEntry source entry.record node child index occupied) entry.record nextIndex
    evaluateHOLFiniteState source branchChildren=(none,next) ∧ View next db cursor.toNat heap.toNat (nextEntry::rest) ∧
      next.locals.lookup (ofString "top")=some (.val (.word entry.record)) ∧
      next.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 nextEntry.data.payload.slotIndex))) ∧
      next.locals.lookup (ofString "mode")=some (.val (.word 2#64)) ∧ next.globals=source.globals ∧
      (∀ name : String,ofString "i"≠ofString name→ ofString "slot"≠ofString name→ ofString "mode"≠ofString name→
        next.locals.lookup (ofString name)=source.locals.lookup (ofString name)) ∧
      (∀ query : BitVec 64,entry.record.toNat+88≤query.toNat→ query.toNat<entry.data.payload.startAddress→ next.memory query=source.memory query) ∧
      next.memaddrs=source.memaddrs ∧ next.be=source.be ∧ next.code=source.code ∧
      WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames (nextEntry::rest)) .resolve true<
        WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames (entry::rest)) .returning true := by
  let nextIndex : Fin 16:=⟨index.val+1,inside⟩
  let nextOccupied:=occupiedNext index occupied used child
  let nextEntry:={entry with data:={entry.data with payload:=.branch node nextIndex nextOccupied}}
  let ready:=branchCounterEntry source entry.record node child index occupied
  let next:=advanced ready entry.record nextIndex
  have head:=view.records entry List.mem_cons_self
  obtain ⟨run,nextRecord,bounded,globals,domain,clock⟩:=branch_children_next source entry.record db node child oldSlot oldMode entry.data index occupied used inside
    head payload topCell branchCell indexCell resultCell slotCell modeCell
  have owned:=head.owned
  simp only [payload,WitnessRecord.Payload.Owned] at owned
  have recordUpper:=head.ceiling
  have nodeUpper:=owned.1.upper
  have indexBound:=index.isLt
  have childNumber : (WitnessRecord.childAddress node index).toNat=node.toNat+(32+8*index.val):=
    byteAddress_toNat node (32+8*index.val) (by omega)
  have indexNumber : (entry.record+32#64).toNat=entry.record.toNat+32:=byteAddress_toNat entry.record 32 (by omega)
  have occupiedNumber : (entry.record+40#64).toNat=entry.record.toNat+40:=byteAddress_toNat entry.record 40 (by omega)
  have bandMemory (query : BitVec 64) (first : entry.record.toNat+88≤query.toNat) (last : query.toNat<entry.data.payload.startAddress) : next.memory query=source.memory query:=by
    change query.toNat<entry.data.payload.startAddress at last
    rw [payload] at last
    change query.toNat<node.toNat at last
    apply branch_next_memory source entry.record node child index occupied nextIndex query
    · intro same; have numeric:=congrArg BitVec.toNat same; rw [childNumber] at numeric; omega
    · intro same; have numeric:=congrArg BitVec.toNat same; rw [occupiedNumber] at numeric; omega
    · intro same; have numeric:=congrArg BitVec.toNat same; rw [indexNumber] at numeric; omega
  have tail:=view.return_tail_frame source next db cursor.toNat heap.toNat cursor.toNat heap.toNat entry rest (Nat.le_refl _) (Nat.le_refl _) domain bandMemory
  have nodeLower : 2713731432≤node.toNat:=by simpa only [payload,WitnessRecord.Payload.startAddress] using head.payloadFloor
  have auxiliary (query : BitVec 64) (offset : Nat) (number : query.toNat=entry.record.toNat+offset) (small : offset<88)
      (not32 : offset≠32) (not40 : offset≠40) : next.memory query=source.memory query:=by
    apply branch_next_memory source entry.record node child index occupied nextIndex query
    · intro same; have numeric:=congrArg BitVec.toNat same; rw [number,childNumber] at numeric; omega
    · intro same; have numeric:=congrArg BitVec.toNat same; rw [number,occupiedNumber] at numeric; omega
    · intro same; have numeric:=congrArg BitVec.toNat same; rw [number,indexNumber] at numeric; omega
  have previous : next.memory entry.record=.word (top rest):=
    (auxiliary entry.record 0 (by omega) (by decide) (by decide) (by decide)).trans view.links.1
  have pending : Pending next db nextEntry:=by
    have old:=view.pending entry List.mem_cons_self
    cases pendingEq : entry.pending with
    | none=>simpa only [Pending,nextEntry,pendingEq] using True.intro
    | some hash=>
      simp only [Pending,pendingEq] at old
      simp only [Pending,nextEntry,pendingEq]
      have number : (entry.record+80#64).toNat=entry.record.toNat+80:=byteAddress_toNat entry.record 80 (by omega)
      exact ⟨(auxiliary _ 80 number (by decide) (by decide) (by decide)).trans old.1,old.2⟩
  have before : nextEntry.data.BeforeHeap nextEntry.mark:=by
    simpa only [nextEntry,WitnessRecord.Description.BeforeHeap,payload,WitnessRecord.Payload.endAddress] using view.before entry List.mem_cons_self
  have order : ∀ parent∈rest,nextEntry.record.toNat+88≤parent.record.toNat ∧ parent.mark≤nextEntry.data.array.toNat ∧ parent.mark≤nextEntry.data.payload.startAddress:=by
    simpa only [nextEntry,payload,WitnessRecord.Payload.startAddress] using view.ordered.1
  have nextView:=View.cons next db cursor.toNat heap.toNat nextEntry rest tail nextRecord before (view.marks entry List.mem_cons_self)
    (view.above entry List.mem_cons_self) previous pending order bounded
  have fields:=advanced_fields ready entry.record nextIndex
  have other (name : String) (notI : ofString "i"≠ofString name) (notSlot : ofString "slot"≠ofString name) (notMode : ofString "mode"≠ofString name) :
      next.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    (advanced_other ready entry.record nextIndex name notSlot notMode).trans (branch_counter_entry_local source entry.record node child index occupied name notI)
  have rank : WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames (nextEntry::rest)) .resolve true<
      WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames (entry::rest)) .returning true:=by
    simpa only [frames,List.map_cons,nextEntry,payload,WitnessRecord.Payload.frame] using branch_next_rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames rest) index inside
  have endian : next.be=source.be:=by unfold next ready advanced branchCounterEntry occupancyState; split <;> rfl
  have code : next.code=source.code:=by unfold next ready advanced branchCounterEntry occupancyState; split <;> rfl
  exact ⟨run,nextView,(other "top" (by decide) (by decide) (by decide)).trans topCell,fields.1,fields.2.1,globals,other,bandMemory,domain,endian,code,rank⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_next_memory
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.branch_children_next_stack
