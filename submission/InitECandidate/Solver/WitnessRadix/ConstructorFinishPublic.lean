import InitECandidate.Solver.WitnessRadix.HelperCallPublic

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact BackingLayout
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The literal constructor's final helper call and table return, from the
completed initialized-array invariant. -/
theorem finish_public {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (valid : Valid layout) (mapped : Mapped source layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (fixedData : FixedData source layout sliceFor) (prefixData : Prefix source layout keyFor layout.count)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word layout.table)))
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 layout.count))))
    (code : source.code.lookup (ofString "solver_radix_index") = some (BuildEntry.formals, BuildProgram.body, .one))
    (enough : 1028 * layout.count + 1 ≤ source.clock) :
    ∃ target : PanSemStateFiniteExact 64 F, ∃ root : BitVec 64,
      evaluateHOLFiniteState source afterRecords = (some (.returned (.val (.word layout.table))), target) ∧
      target.memaddrs (cell layout .header 24) ∧ target.memory (cell layout .header 24) = .word root ∧
      QueryMemory.Represents target layout.table layout.keys layout.vals root
        (initialTree keyFor sliceFor (ordinals layout.count)) ∧
      control target = control source ∧ source.clock - (1028 * layout.count + 1) ≤ target.clock ∧
      target.clock ≤ source.clock ∧
      (∀ query,PublicWord layout query→target.memory query=source.memory query) := by
  classical
  obtain ⟨post, root, callRun, locals, rootMapped, rootWord, represented, controls, lower, upper,publicMemory⟩ :=
    helper_call_public source layout valid mapped keyFor sliceFor fixedData prefixData tableLocal countLocal code enough
  have table : post.locals.lookup (ofString "t") = some (.val (.word layout.table)) := by rw [locals]; exact tableLocal
  have returned : evaluateHOLFiniteState post (.return (localVar "t")) =
      (some (.returned (.val (.word layout.table))), emptyLocalsHOLFinite post) := by
    simp [evaluateHOLFiniteState_return, localVar, evalHOLExact, toExact, table, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have run := (StateSteps.next_sequence source post helperCall (.return (localVar "t")) callRun upper).trans returned
  let target := emptyLocalsHOLFinite post
  refine ⟨target, root, run, rootMapped, rootWord, ?_, controls, lower, upper,publicMemory⟩
  exact QueryMemory.represents_of_fields post target rfl rfl rfl _ _ _ _ _ represented

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.finish_public
