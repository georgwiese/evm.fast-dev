import InitECandidate.Solver.Mpt.WitnessCoreStackFrame
import InitECandidate.Solver.Mpt.WitnessCoreResultNode
import InitECandidate.Solver.Input.CurrentTable.NodeLookup.Returned

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- A returned node follows the current head's allocation mark. The
ordered real allocations imply the same separation from every older
frame, so caching its pending hash preserves the entire active stack. -/
theorem cache (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db child hash : BitVec 64)
    (cursor heap : Nat) (heapBound : heap≤2952790016) (entry : Entry) (rest : List Entry) (view : View source db cursor heap (entry::rest))
    (owned : ResultOwned source entry.mark heap child) :
    View (returnCacheState source child hash) db cursor heap (entry::rest) := by
  rcases owned with zero|allocated
  · rw [returnCacheState,if_pos (Or.inr zero)]
    exact view
  · let target:=returnCacheState source child hash
    have head:=view.records entry List.mem_cons_self
    have headBefore:=view.before entry List.mem_cons_self
    have nodePersistent : child.toNat+32≤2952790016:=allocated.before.trans heapBound
    have nodeUpper:=allocated.arena.upper
    have nodeNumber : (child+24#64).toNat=child.toNat+24:=byteAddress_toNat child 24 (by omega)
    have marks (current : Entry) (member : current∈entry::rest) : current.mark≤entry.mark:=by
      rcases List.mem_cons.mp member with same|older
      · subst current; exact Nat.le_refl _
      · have order:=view.ordered.1 current older
        have upper:=headBefore.1
        omega
    have recordMemory (current : Entry) (member : current∈entry::rest) : target.memory current.record=source.memory current.record:=by
      have bound:=(view.records current member).scratchLower
      have away : current.record≠child+24#64:=by intro same; have numeric:=congrArg BitVec.toNat same; rw [nodeNumber] at numeric; omega
      exact return_cache_memory source child hash current.record away
    have records (current : Entry) (member : current∈entry::rest) : WitnessRecord.View target current.record db current.data:=by
      have before:=(view.before current member).mono current.data current.mark child.toNat ((marks current member).trans allocated.fresh)
      exact return_cache_view source current.record db child hash current.data (view.records current member)
        (Or.inr ⟨allocated.arena,allocated.aligned⟩) (fun _ _=>⟨nodePersistent,before⟩)
    have pending (current : Entry) (member : current∈entry::rest) : Pending target db current:=by
      have old:=view.pending current member
      cases pendingEq : current.pending with
      | none=>simp [Pending,pendingEq]
      | some value=>
        simp only [Pending,pendingEq] at old ⊢
        have bound:=(view.records current member).scratchLower
        have recordUpper:=(view.records current member).arena.upper
        have recordNumber : (current.record+80#64).toNat=current.record.toNat+80:=byteAddress_toNat current.record 80 (by omega)
        have away : current.record+80#64≠child+24#64:=by
          intro same
          have numeric:=congrArg BitVec.toNat same
          rw [recordNumber,nodeNumber] at numeric
          omega
        exact ⟨(return_cache_memory source child hash (current.record+80#64) away).trans old.1,old.2⟩
    exact ⟨records,view.before,view.marks,view.above,view.links.frame source target (entry::rest) recordMemory,pending,view.ordered,view.counters⟩

/-- The real child-cache store cannot change memory before the returned
node's allocation frontier. This protects the fixed input databases even
though a general before-current-heap frame would be false. -/
theorem cache_memory_before (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child hash : BitVec 64)
    (lower upper : Nat) (owned : ResultOwned source lower upper child)
    (query : BitVec 64) (before : query.toNat<lower) :
    (returnCacheState source child hash).memory query=source.memory query := by
  rcases owned with zero|allocated
  · rw [returnCacheState,if_pos (Or.inr zero)]
  · have bound:=allocated.arena.upper
    have fresh:=allocated.fresh
    have number : (child+24#64).toNat=child.toNat+24:=byteAddress_toNat child 24 (by omega)
    exact return_cache_memory source child hash query (by
      intro same
      have numeric:=congrArg BitVec.toNat same
      rw [number] at numeric
      omega)

/-- The actual Patricia image and input rows survive the completed-child
cache store whenever their already-built table precedes that frontier. -/
theorem cache_database (data : Input.CurrentTable.NodeBuild.Data)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child hash : BitVec 64)
    (lower upper : Nat) (database : Input.CurrentTable.NodeLookup.Database source data)
    (tableBefore : (Input.CurrentTable.New.endPointer data.table data.cap).toNat≤lower)
    (owned : ResultOwned source lower upper child) :
    Input.CurrentTable.NodeLookup.Database (returnCacheState source child hash) data := by
  apply database.of_before lower tableBefore
  · unfold returnCacheState; split <;> rfl
  · unfold returnCacheState; split <;> rfl
  · exact cache_memory_before source child hash lower upper owned

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.cache

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.cache_memory_before
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.cache_database
