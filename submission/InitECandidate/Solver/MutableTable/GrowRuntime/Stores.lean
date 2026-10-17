import InitECandidate.Solver.MutableTable.GrowRuntime.Clear
import InitECandidate.Solver.PanFieldStores

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def resetFields (plan : Plan) : List FieldStores.Field :=
  [⟨16, .saved "ncap" (BitVec.ofNat 64 plan.capacity)⟩, ⟨32, .saved "nkeys" (cell plan .keys 0)⟩,
   ⟨40, .saved "nvals" (cell plan .values 0)⟩, ⟨48, .saved "nused" (cell plan .used 0)⟩,
   ⟨56, .saved "norder" (cell plan .order 0)⟩, ⟨64, .saved "norder_pos" (cell plan .position 0)⟩,
   ⟨24, .literal 0#64⟩]

theorem reset_program (plan : Plan) :
    WitnessRadix.ProgramPrefix.program (Grow.actions.drop 13) Grow.afterSetup = FieldStores.program "t" "" (resetFields plan) Grow.afterSetup := by
  simp only [Grow.actions, List.drop, List.drop_zero, WitnessRadix.ProgramPrefix.program, FieldStores.program,
    resetFields, FieldStores.address, FieldStores.Value.expression, Grow.headerStore, addConst]

theorem reset_writes (plan : Plan) : FieldStores.writes (cell plan .header 0) (resetFields plan) = resetWrites plan := by
  simp [FieldStores.writes, resetFields, FieldStores.Value.word, resetWrites, constant_cell]

/-- Seven actual growth header stores, with an arbitrary continuation and
all its outcomes. Saved allocation results supply their real values. -/
theorem stores_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (capLocal : source.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (keyLocal : source.locals.lookup (ofString "nkeys") = some (.val (.word (cell plan .keys 0))))
    (valueLocal : source.locals.lookup (ofString "nvals") = some (.val (.word (cell plan .values 0))))
    (usedLocal : source.locals.lookup (ofString "nused") = some (.val (.word (cell plan .used 0))))
    (orderLocal : source.locals.lookup (ofString "norder") = some (.val (.word (cell plan .order 0))))
    (positionLocal : source.locals.lookup (ofString "norder_pos") = some (.val (.word (cell plan .position 0))))
    (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (FieldStores.program "t" "" (resetFields plan) continuation) =
      evaluateHOLFiniteState {source with memory := WordWrites.write source.memory (resetWrites plan)} continuation := by
  rw [← reset_writes]
  apply FieldStores.execute source "t" "" (cell plan .header 0) 0#64 (resetFields plan) tableLocal
  · intro field member
    simp only [resetFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | assumption | trivial
  · intro field member
    rw [domain, constant_cell]
    apply mapped kind plan valid .header
    · simp only [resetFields, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [size]
    · simp only [resetFields, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [size]
  · intro reader member writer writerMember
    simp only [resetFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.reset_program
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.reset_writes
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.stores_execute
