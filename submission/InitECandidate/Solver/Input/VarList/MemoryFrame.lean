import InitECandidate.Solver.Input.VarList.Walk

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact WitnessRadix.QueryBranch

def Outside {input : Guest.InputBlob} (plan : Plan input) (query : BitVec 64) : Prop :=
  query.toNat<plan.array.toNat ∨ plan.array.toNat+16*plan.count≤query.toNat

def ArrayFrame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input) : Prop :=
  ∀ query,Outside plan query→target.memory query=source.memory query

theorem ArrayFrame.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input) : ArrayFrame source source input plan := by
  intro query outside
  rfl

theorem ArrayFrame.trans {source middle target : PanSemStateFiniteExact 64 Guest.HostMemory} {input : Guest.InputBlob} {plan : Plan input}
    (first : ArrayFrame source middle input plan) (second : ArrayFrame middle target input plan) : ArrayFrame source target input plan := by
  intro query outside
  exact (second query outside).trans (first query outside)

theorem ArrayFrame.of_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (memory : target.memory=source.memory) : ArrayFrame source target input plan := by
  intro query outside
  rw [memory]

theorem ArrayFrame.restore (saved source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (name : String) (frame : ArrayFrame source target input plan) : ArrayFrame source (WitnessRadix.QueryBranch.restore saved name target) input plan := by
  intro query outside
  exact frame query outside

theorem Plan.row_inside {input : Guest.InputBlob} (plan : Plan input) (index : Nat) (small : index<plan.count) :
    plan.array.toNat≤(row plan.array index).toNat ∧ (row plan.array index).toNat<plan.array.toNat+16*plan.count := by
  rw [plan.row_nat index small]
  omega

theorem Plan.length_inside {input : Guest.InputBlob} (plan : Plan input) (index : Nat) (small : index<plan.count) :
    plan.array.toNat≤(lengthCell plan.array index).toNat ∧ (lengthCell plan.array index).toNat<plan.array.toNat+16*plan.count := by
  rw [plan.length_nat index small]
  omega

theorem outside_ne_inside {input : Guest.InputBlob} (plan : Plan input) (query address : BitVec 64) (outside : Outside plan query)
    (inside : plan.array.toNat≤address.toNat ∧ address.toNat<plan.array.toNat+16*plan.count) : query≠address := by
  intro eq
  rw [eq] at outside
  unfold Outside at outside
  omega

/-- Every actual word write in this decoder is confined to its fresh array. -/
theorem store_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (address value : BitVec 64) (inside : plan.array.toNat≤address.toNat ∧ address.toNat<plan.array.toNat+16*plan.count) :
    ArrayFrame source {source with memory:=WitnessRadix.StoreWord.put source.memory address value} input plan := by
  intro query outside
  simp only [WitnessRadix.StoreWord.put,if_neg (outside_ne_inside plan query address outside inside)]

theorem iteration_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (small : index<plan.count) (previous : BitVec 64) : ArrayFrame source (iteration source input plan index previous) input plan := by
  intro query outside
  have rowAway:=outside_ne_inside plan query (row plan.array index) outside (plan.row_inside index small)
  change WitnessRadix.StoreWord.put
    (if 0<index then WitnessRadix.StoreWord.put source.memory (lengthCell plan.array (index-1)) (currentWord input plan.start index-previous) else source.memory)
    (row plan.array index) (plan.inputPointer+BitVec.ofNat 64 plan.start+currentWord input plan.start index) query=source.memory query
  by_cases positive : 0<index
  · have lengthAway:=outside_ne_inside plan query (lengthCell plan.array (index-1)) outside (plan.length_inside (index-1) (by omega))
    simp only [if_pos positive,WitnessRadix.StoreWord.put,if_neg rowAway,if_neg lengthAway]
  · simp only [if_neg positive,WitnessRadix.StoreWord.put,if_neg rowAway]

theorem failed_iteration_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input) (index : Nat) :
    ArrayFrame source (failedIteration source input plan index) input plan := by
  intro query outside
  rfl

theorem walk_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index rounds : Nat) (inside : index+rounds≤plan.count) (previous : BitVec 64) : ArrayFrame source (walk source input plan index previous rounds) input plan := by
  induction rounds generalizing source index previous with
  | zero=>exact ArrayFrame.refl _ _ _
  | succ rounds ih=>
    have head : ArrayFrame source (iteration (decClockHOLFinite source) input plan index previous) input plan := by
      intro query outside
      exact iteration_frame (decClockHOLFinite source) input plan index (by omega) previous query outside
    have tail:=ih (iteration (decClockHOLFinite source) input plan index previous) (index+1) (by omega) (currentWord input plan.start index)
    exact head.trans tail

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.ArrayFrame.refl
#print axioms InitECandidate.Solver.Input.VarList.ArrayFrame.trans
#print axioms InitECandidate.Solver.Input.VarList.ArrayFrame.of_memory
#print axioms InitECandidate.Solver.Input.VarList.ArrayFrame.restore
#print axioms InitECandidate.Solver.Input.VarList.Plan.row_inside
#print axioms InitECandidate.Solver.Input.VarList.Plan.length_inside
#print axioms InitECandidate.Solver.Input.VarList.outside_ne_inside
#print axioms InitECandidate.Solver.Input.VarList.store_frame
#print axioms InitECandidate.Solver.Input.VarList.iteration_frame
#print axioms InitECandidate.Solver.Input.VarList.failed_iteration_frame
#print axioms InitECandidate.Solver.Input.VarList.walk_frame
