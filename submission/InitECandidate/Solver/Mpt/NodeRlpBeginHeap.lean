import InitECandidate.Solver.Mpt.NodeRlpBeginCall
import InitECandidate.Solver.Mpt.TrieWalkValueAgreement
import InitECandidate.Solver.Mpt.TrieGraphRegisteredRegions
import InitECandidate.Solver.PanHeapGlobals

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Scratch records beyond the incoming heap preserve the actual begin
entry graph and value fields. The new graph is constructed from that
memory agreement rather than assumed at the later call. -/
theorem Entry.of_before {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap : BitVec 64}
    {lower limit : Nat} {property : BitVec 64→BitVec 64→Prop}
    (data : Entry source node heap lower limit property)
    (domain : target.memaddrs=source.memaddrs)
    (heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (memory : ∀ query : BitVec 64,query.toNat<heap.toNat→target.memory query=source.memory query) :
    Nonempty (Entry target node heap lower limit property) := by
  have structural : ∀ query,data.graph.Footprint query→target.memory query=source.memory query:=
    fun query required=>memory query (data.graph.footprint_bounds lower heap.toNat data.regions query required).2
  let next:=data.graph.of_agreement source.memory target.memory source.memaddrs target.memaddrs domain structural
  have same : next.valid=data.graph.valid:=rfl
  have tags (current : BitVec 64) (member : data.graph.valid current) (active : current≠0#64) :
      wordAt target.memory current=wordAt source.memory current:=
    congrArg MemoryBytes.wordBits (structural current (.header current member active))
  have values:=data.values.of_agreement source.memory target.memory source.memaddrs target.memaddrs data.graph next limit
    same domain tags (fun query required=>memory query (data.graph.value_bounds lower heap.toNat data.regions query required).2)
  have regions:=data.regions.of_agreement source.memory target.memory source.memaddrs target.memaddrs data.graph next lower heap.toNat same tags
  exact ⟨{
    graph:=next,member:=data.member,active:=data.active,nonHash:=by rw [tags node data.member data.active]; exact data.nonHash
    values:=values,regions:=regions,heapCell:=heapCell,heapLower:=data.heapLower,heapUpper:=data.heapUpper,
    heapAligned:=data.heapAligned,domain:=domain.trans data.domain }⟩

def outputHeap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node heap : BitVec 64) : BitVec 64:=
  if wordAt source.memory node=3#64 then heap else PersistentAlloc.rounded heap (allocationAmount (wordAt source.memory (node+40#64)))

theorem Output.domain {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64} {limit allowance : Nat} {value : ValueHOL 64}
    (output : Output source target node heap frame limit value allowance) : target.memaddrs=source.memaddrs := by
  have same:=congrArg PanSemStateFiniteExact.memaddrs output.fields
  change target.memaddrs=(preparationBase source node heap).memaddrs at same
  exact same.trans (by unfold preparationBase; split <;> rfl)

theorem Output.endian {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64} {limit allowance : Nat} {value : ValueHOL 64}
    (output : Output source target node heap frame limit value allowance) : target.be=source.be := by
  have same:=congrArg PanSemStateFiniteExact.be output.fields
  change target.be=(preparationBase source node heap).be at same
  exact same.trans (by unfold preparationBase; split <;> rfl)

theorem Output.code {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64} {limit allowance : Nat} {value : ValueHOL 64}
    (output : Output source target node heap frame limit value allowance) : target.code=source.code := by
  have same:=congrArg PanSemStateFiniteExact.code output.fields
  change target.code=(preparationBase source node heap).code at same
  exact same.trans (by unfold preparationBase; split <;> rfl)

theorem Output.heap {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64} {lower limit allowance : Nat}
    {property : BitVec 64→BitVec 64→Prop} {value : ValueHOL 64}
    (output : Output source target node heap frame limit value allowance) (data : Entry source node heap lower limit property) :
    target.globals.lookup (ofString "heap_ptr")=some (.val (.word (outputHeap source node heap))) ∧
      heap.toNat≤(outputHeap source node heap).toNat ∧ (outputHeap source node heap).toNat≤2952790016 ∧ (outputHeap source node heap).toNat%8=0 := by
  have same:=congrArg (fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>current.globals.lookup (ofString "heap_ptr")) output.fields
  change target.globals.lookup (ofString "heap_ptr")=(preparationBase source node heap).globals.lookup (ofString "heap_ptr") at same
  by_cases branch : wordAt source.memory node=3#64
  · simp only [preparationBase,if_pos branch] at same
    simp only [outputHeap,if_pos branch]
    exact ⟨same.trans data.heapCell,Nat.le_refl _,data.heapUpper,data.heapAligned⟩
  · have room:=(output.path branch).2.2.2.2
    have requestRoom : heap.toNat+(allocationAmount (wordAt source.memory (node+40#64))).toNat≤2952790016:=by
      rw [allocation_amount]
      omega
    have bounds:=PersistentAlloc.guards heap (allocationAmount (wordAt source.memory (node+40#64))) requestRoom
    simp only [outputHeap,if_neg branch]
    refine ⟨?_,by have number:=allocation_amount (wordAt source.memory (node+40#64)); omega,bounds.2.2.2.1,bounds.2.2.2.2⟩
    simpa [preparationBase,branch,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE] using same

theorem Output.heap_globals {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {limit allowance : Nat} {value : ValueHOL 64} (output : Output source target node heap frame limit value allowance) :
    HeapGlobals source target := by
  intro key other
  have same:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup key) output.fields
  change target.globals.lookup key=(preparationBase source node heap).globals.lookup key at same
  unfold preparationBase at same
  split at same
  · exact same
  · exact same.trans (HeapGlobals.update source _ key other)

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Output.domain
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Output.endian
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Output.code
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Output.heap
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Entry.of_before
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Output.heap_globals
