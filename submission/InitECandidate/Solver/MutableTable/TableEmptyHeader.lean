import InitECandidate.Solver.MutableTable.TableEmpty

namespace InitECandidate.Solver.MutableTable.TableEmpty
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem entered_before (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (offset : Nat) (before : offset<48) (value : BitVec 64)
    (member : (BitVec.ofNat 64 plan.table+BitVec.ofNat 64 offset,value)∈TableNew.beforeWrites plan) :
    (TableNew.enteredState source plan).memory (BitVec.ofNat 64 plan.table+BitVec.ofNat 64 offset)=.word value := by
  rw [TableNew.entered_memory]
  apply TableNew.result_before source.memory source.be plan ready offset before value
  exact member

/-- The actual completed constructor supplies the original find/get header,
independently of the caller's formal-parameter names. -/
theorem entered_header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain) (key : BitVec 64) :
    Find.HeaderData (TableNew.enteredState source plan) (BitVec.ofNat 64 plan.table) (parameters plan key) := by
  have mapped (offset : Nat) (inside : offset+8≤72) (aligned : offset%8=0) :
      (TableNew.enteredState source plan).memaddrs (BitVec.ofNat 64 plan.table+BitVec.ofNat 64 offset) := by
    exact AllocatedLayout.mapped source plan ready domain .header offset aligned inside
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro offset member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> exact mapped _ (by decide) (by decide)
  · exact entered_before source plan ready 16 (by decide) _ (by simp [TableNew.beforeWrites,parameters])
  · simpa [parameters] using
      entered_before source plan ready 0 (by decide) 32#64 (by simp [TableNew.beforeWrites])
  · exact entered_before source plan ready 8 (by decide) _ (by simp [TableNew.beforeWrites,parameters])
  · exact entered_before source plan ready 32 (by decide) _ (by simp [TableNew.beforeWrites,parameters])
  · rw [TableNew.entered_memory]
    exact TableNew.result_after source.memory source.be plan ready
      (BitVec.ofNat 64 plan.table+48#64,TableNew.usedAddress plan) (by simp [TableNew.afterWrites])

theorem entered_count (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) :
    (TableNew.enteredState source plan).memory (BitVec.ofNat 64 plan.table+24#64)=.word 0#64 :=
  entered_before source plan ready 24 (by decide) 0#64 (by simp [TableNew.beforeWrites])

end InitECandidate.Solver.MutableTable.TableEmpty

#print axioms InitECandidate.Solver.MutableTable.TableEmpty.entered_header
#print axioms InitECandidate.Solver.MutableTable.TableEmpty.entered_count
