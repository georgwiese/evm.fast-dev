import InitECandidate.Solver.MutableTable.OccupiedValueProperty

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack PanSemStateFiniteExact

theorem OccupiedValuesHave.of_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (vals capacity : BitVec 64) (slots : List Nat) (property : BitVec 64 → Prop)
    (values : OccupiedValuesHave source vals capacity slots property)
    (same : source.memory=target.memory) : OccupiedValuesHave target vals capacity slots property := by
  apply values.of_agreement source target vals capacity slots property
  intro slot inside member
  rw [same]

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.OccupiedValuesHave.of_memory
