import InitECandidate.Solver.Input.CurrentTable.NodeBuild.BodyCost

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack PanSemStateFiniteExact

theorem ReachesTable.count_bound {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {count lower : Nat}
    {stp pad : BitVec 64} {outcome : Option (PanSemResultExact 64)}
    (reaches : ReachesTable source post count lower stp pad outcome) : count≤1048575 := by
  obtain ⟨selected,target,inner,heap,bits,bitsLower,bitsUpper,sufficient,capBound,countBound,rest⟩ := reaches
  exact countBound

/-- Inputs exceeding the actual allocation-derived count limit cannot
reach the expensive loop. Their genuine stopped prefix still costs≤36. -/
theorem body_capped_byte_cost (data : Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry data source) (bytes : Nat)
    (budget : VarList.sumPrefix (fun index=>(data.lengths index).toNat) data.total≤bytes)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤44*(bytes/136)+1507*(min data.total 1048575)+36 := by
  by_cases small : data.total≤1048575
  · rw [Nat.min_eq_left small]
    exact body_byte_cost data source post entry bytes budget outcome run
  · rcases constructor_trace source post data.total data.upper data.stp data.pad entry.workspace entry.totalSmall entry.countCell outcome run with stopped|reached
    · omega
    · exact False.elim (small reached.count_bound)

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.body_capped_byte_cost
