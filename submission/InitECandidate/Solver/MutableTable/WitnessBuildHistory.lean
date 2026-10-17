import InitECandidate.Solver.MutableTable.WitnessBuildProgram

namespace InitECandidate.Solver.MutableTable.WitnessBuild

/-- Observed digest/record history in actual input ordinal order. Digests may
repeat arbitrarily; every value is the corresponding real slice-record address. -/
inductive History (plan : WitnessRadix.AllocatedLayout.Plan) : List (Find.Key32×BitVec 64)→Prop where
  | empty : History plan []
  | snoc (input : List (Find.Key32×BitVec 64)) (prior : History plan input) (key : Find.Key32)
      (inside : input.length<plan.count) : History plan (input++[(key,recordAddress plan input.length)])

theorem History.length_bound (plan : WitnessRadix.AllocatedLayout.Plan) (input : List (Find.Key32×BitVec 64))
    (history : History plan input) : input.length≤plan.count := by
  cases history with
  | empty=>simp
  | snoc input prior key inside=>simp only [List.length_append,List.length_singleton];omega

/-- Every represented history value points to a real input slice record. -/
theorem History.value_record (plan : WitnessRadix.AllocatedLayout.Plan) (input : List (Find.Key32×BitVec 64))
    (history : History plan input) (key : Find.Key32) (value : BitVec 64) (member : (key,value)∈input) :
    ∃ i<plan.count,value=recordAddress plan i := by
  induction history with
  | empty=>simp at member
  | snoc input prior next inside ih=>
    rcases List.mem_append.mp member with old|last
    · exact ih old
    · simp only [List.mem_singleton,Prod.mk.injEq] at last
      exact ⟨input.length,inside,last.2⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.History.length_bound
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.History.value_record
