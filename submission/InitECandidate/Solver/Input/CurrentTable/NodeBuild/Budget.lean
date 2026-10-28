import InitECandidate.Solver.Input.CurrentTable.NodeBuild.Loop
import InitECandidate.Solver.Input.VarList.RecordByteBudget

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack PanSemStateFiniteExact
open scoped BigOperators

private theorem prefix_sum (f : Nat → Nat) (count : Nat) :
    (∑ index ∈ Finset.range count,f index)=VarList.sumPrefix f count := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [Finset.sum_range_succ,VarList.sumPrefix] using congrArg (fun total=>total+f count) ih

private theorem floor_sum (f : Nat → Nat) (count : Nat) :
    (∑ index ∈ Finset.range count,f index/136)≤(∑ index ∈ Finset.range count,f index)/136 := by
  induction count with
  | zero => simp
  | succ count ih =>
    simp only [Finset.sum_range_succ]
    exact (Nat.add_le_add_right ih _).trans Nat.div_add_div_le_add_div

private theorem price_sum (f : Nat → Nat) (count : Nat) :
    (∑ index ∈ Finset.range count,(44*(f index/136)+1507))=
      44*(∑ index ∈ Finset.range count,f index/136)+1507*count := by
  induction count with
  | zero => simp
  | succ count ih =>
    simp only [Finset.sum_range_succ,Nat.mul_succ,Nat.mul_add,ih]
    omega

/-- Hash work is charged once to aggregate actual payload bytes. The
fixed insertion/loop overhead is charged once per real decoded record. -/
theorem remaining_byte_bound (data : Data) (bytes : Nat)
    (budget : VarList.sumPrefix (fun index=>(data.lengths index).toNat) data.total≤bytes) :
    remainingFrom data 0≤44*(bytes/136)+1507*data.total := by
  have floors := floor_sum (fun index=>(data.lengths index).toNat) data.total
  rw [prefix_sum (fun index=>(data.lengths index).toNat) data.total] at floors
  have bytesBound : VarList.sumPrefix (fun index=>(data.lengths index).toNat) data.total/136≤bytes/136 := Nat.div_le_div_right budget
  have countBound : (∑ index ∈ Finset.range data.total,(data.lengths index).toNat/136)≤bytes/136 := floors.trans bytesBound
  calc
    remainingFrom data 0 = 44*(∑ index ∈ Finset.range data.total,(data.lengths index).toNat/136)+1507*data.total := by
      simpa only [remainingFrom,Nat.Ico_zero_eq_range] using price_sum (fun index=>(data.lengths index).toNat) data.total
    _ ≤ 44*(bytes/136)+1507*data.total := Nat.add_le_add_right (Nat.mul_le_mul_left 44 countBound) _

theorem loop_byte_cost (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (state : State data origin source 0) (layout : Layout data) (bytes : Nat)
    (budget : VarList.sumPrefix (fun index=>(data.lengths index).toNat) data.total≤bytes) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤44*(bytes/136)+1507*data.total :=
  (loop_cost data origin source 0 state layout (by omega)).trans (remaining_byte_bound data bytes budget)

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.remaining_byte_bound
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.loop_byte_cost
