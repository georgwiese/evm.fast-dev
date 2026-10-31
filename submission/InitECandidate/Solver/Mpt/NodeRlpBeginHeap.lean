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


/-- The actual three descriptor stores retain the exact prepared payload
at a real high scratch frame. The leaf byte decision only needs its actual
incoming backing word below the persistent cap. -/
theorem Output.path_payload {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {lower limit allowance : Nat} {property : BitVec 64 → BitVec 64 → Prop} {value : ValueHOL 64}
    (output : Output source target node heap frame limit value allowance) (data : Entry source node heap lower limit property)
    (notBranch : wordAt source.memory node≠3#64) (frameHigh : 2952790016≤frame.toNat) (frameFits : frame.toNat+48<2^64)
    (valueLow : wordAt source.memory node=1#64 → wordAt source.memory (node+56#64)=1#64 →
      (panByteAlignHOL (width:=64) (wordAt source.memory (node+48#64))).toNat<2952790016) :
    PathPayload target node (wordAt source.memory node) output.buffer output.length output.payload := by
  obtain ⟨prepared,memory,fields,sized,older⟩:=output.sizingTrace
  have nodeWordBefore (offset : Nat) (inside : offset<64) (leaf : wordAt source.memory node=1#64) :
      (byteAddress node offset).toNat<heap.toNat:=
    (data.graph.region_query_bounds lower heap.toNat data.regions node offset data.member data.active (by rw [leaf]; exact inside)).2
  have footprintLow : ∀ query,PathPayload.Footprint prepared node (wordAt source.memory node) output.buffer output.length query → query.toNat<2952790016:=by
    intro query required
    rcases required with ⟨leaf,equal|equal⟩|⟨_one,equal⟩|⟨leaf,one,equal⟩
    · rw [equal]
      have bound:=nodeWordBefore 48 (by decide) leaf
      change (node+48#64).toNat<heap.toNat at bound
      have cap:=data.heapUpper
      omega
    · rw [equal]
      have bound:=nodeWordBefore 56 (by decide) leaf
      change (node+56#64).toNat<heap.toNat at bound
      have cap:=data.heapUpper
      omega
    · have path:=output.path notBranch
      have bufferEq:=path.1
      have room:=path.2.2.2.2
      rw [equal,bufferEq,AllocatedBytes.aligned_number]
      omega
    · have pointerMemory:=older (node+48#64) (nodeWordBefore 48 (by decide) leaf)
      have lengthMemory:=older (node+56#64) (nodeWordBefore 56 (by decide) leaf)
      have pointerWord:=congrArg MemoryBytes.wordBits pointerMemory
      have lengthWord:=congrArg MemoryBytes.wordBits lengthMemory
      change wordAt prepared.memory (node+48#64)=wordAt source.memory (node+48#64) at pointerWord
      change wordAt prepared.memory (node+56#64)=wordAt source.memory (node+56#64) at lengthWord
      rw [equal,pointerWord]
      exact valueLow leaf (by rwa [lengthWord] at one)
  have domain:=congrArg PanSemStateFiniteExact.memaddrs fields
  have endian:=congrArg PanSemStateFiniteExact.be fields
  change target.memaddrs=prepared.memaddrs at domain
  change target.be=prepared.be at endian
  apply (sized notBranch).of_memory domain endian
  intro query required
  have low:=footprintLow query required
  have away (offset : Nat) (inside : offset<48) : query≠frame+BitVec.ofNat 64 offset:=by
    have number:=byteAddress_toNat frame offset (by omega)
    intro equal
    have numeric:=congrArg BitVec.toNat equal
    change query.toNat=(byteAddress frame offset).toNat at numeric
    rw [number] at numeric
    omega
  rw [memory]
  exact stored_away prepared.memory frame output.buffer output.length output.payload query (away 24 (by decide)) (away 32 (by decide)) (away 40 (by decide))

/-- The actual earlier-input value property places a required one-byte
leaf decision below the persistent cap; every other value length is irrelevant. -/
theorem Entry.value_byte_low {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap : BitVec 64} {lower limit inputEnd : Nat}
    (data : Entry source node heap lower limit (fun pointer length=>pointer.toNat+length.toNat≤inputEnd)) (inputBefore : inputEnd≤2952790016)
    (leaf : wordAt source.memory node=1#64) (one : wordAt source.memory (node+56#64)=1#64) :
    (panByteAlignHOL (width:=64) (wordAt source.memory (node+48#64))).toNat<2952790016 := by
  let view:=data.values.leaf node data.member data.active leaf
  have pointerWord : wordAt source.memory (node+48#64)=view.pointer:=by simp [wordAt,view.pointerStored,MemoryBytes.wordBits]
  have lengthWord : wordAt source.memory (node+56#64)=view.length:=by simp [wordAt,view.lengthStored,MemoryBytes.wordBits]
  have lengthOne : view.length.toNat=1:=by rw [←lengthWord,one]; rfl
  rw [pointerWord,AllocatedBytes.aligned_number]
  have bound:=view.extra
  omega

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Output.domain
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Output.endian
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Output.code
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Output.heap
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Entry.of_before
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Output.heap_globals

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Output.path_payload

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Entry.value_byte_low
