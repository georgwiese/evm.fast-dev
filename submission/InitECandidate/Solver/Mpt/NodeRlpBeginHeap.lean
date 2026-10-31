import InitECandidate.Solver.Mpt.NodeRlpBeginCall

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

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

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Output.domain
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Output.endian
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Output.code
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Output.heap
