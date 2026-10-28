import InitECandidate.Solver.Input.CurrentTable.NodeBuild.Entry
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.Budget

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Every outcome of the complete unchanged current database builder fits
its capacity/constructor prefix and the sum of actual insertion allowances.
No successful future table allocation or iteration is an entry assumption. -/
theorem body_cost (data : Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry data source) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤36+remainingFrom data 0 := by
  rcases constructor_trace source post data.total data.upper data.stp data.pad entry.workspace entry.totalSmall entry.countCell outcome run with stopped|reached
  · exact Nat.le_trans stopped (by omega)
  · obtain ⟨selected,target,inner,heap,bits,bitsLower,bitsUpper,sufficient,capBound,countBound,heapLower,returned,workspace,same,others,earlier,forward,clock,continued,endpoint⟩ := reached
    have selectedEntry := entry.of_frame same ((others (ofString "slice_arr") (by decide)).trans entry.arrayCell)
      ((others (ofString "n") (by decide)).trans entry.countCell)
    have capNumber : (BitVec.ofNat 64 (2^bits)).toNat=2^bits := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
    let currentData : Data := {data with table:=heap,cap:=BitVec.ofNat 64 (2^bits)}
    have layout : Layout currentData := selectedEntry.at_table heap (BitVec.ofNat 64 (2^bits)) (by rw [capNumber]; exact sufficient) heapLower
    have price := table_tail_cost currentData selected target returned layout selectedEntry.little selectedEntry.rows selectedEntry.outCell selectedEntry.arrayCell selectedEntry.countCell
    rw [continued] at price
    change target.clock-inner.clock≤remainingFrom data 0 at price
    have postClock : post.clock=inner.clock := by rw [endpoint]; rfl
    rw [postClock]
    omega

/-- The complete actual body is linear in aggregate decoded payload bytes
and actual record count. Straight-line target work is priced separately. -/
theorem body_byte_cost (data : Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry data source) (bytes : Nat)
    (budget : VarList.sumPrefix (fun index=>(data.lengths index).toNat) data.total≤bytes)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤44*(bytes/136)+1507*data.total+36 := by
  have cost := body_cost data source post entry outcome run
  have allowance := remaining_byte_bound data bytes budget
  omega

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.body_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.body_byte_cost
