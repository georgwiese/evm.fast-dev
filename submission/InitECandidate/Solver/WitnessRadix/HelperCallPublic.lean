import InitECandidate.Solver.WitnessRadix.HelperCall
import InitECandidate.Solver.WitnessRadix.HelperBuiltPublic

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact BackingLayout
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Actual helper call from completed constructor arrays, including real
argument/code lookup, callee entry and caller-local restoration. -/
theorem helper_call_public {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (valid : Valid layout) (mapped : Mapped source layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (fixedData : FixedData source layout sliceFor) (prefixData : Prefix source layout keyFor layout.count)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word layout.table)))
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 layout.count))))
    (code : source.code.lookup (ofString "solver_radix_index") = some (BuildEntry.formals, BuildProgram.body, .one))
    (enough : 1028 * layout.count + 1 ≤ source.clock) :
    ∃ target : PanSemStateFiniteExact 64 F, ∃ root : BitVec 64,
      evaluateHOLFiniteState source helperCall = (none, target) ∧
      target.locals = source.locals ∧ target.memaddrs (cell layout .header 24) ∧
      target.memory (cell layout .header 24) = .word root ∧
      QueryMemory.Represents target layout.table layout.keys layout.vals root
        (initialTree keyFor sliceFor (ordinals layout.count)) ∧
      control target = control source ∧ source.clock - (1028 * layout.count + 1) ≤ target.clock ∧
      target.clock ≤ source.clock ∧
      (∀ query,PublicWord layout query→target.memory query=source.memory query) := by
  classical
  obtain ⟨callee, lookup, table, count⟩ := BuildEntry.environment source.code.lookup layout.table (BitVec.ofNat 64 layout.count) code
  let entry := callEntryStateHOLFinite source callee
  have prefix' := prefix_of_fields source entry layout keyFor layout.count rfl rfl rfl prefixData
  have fixed' := fixed_of_fields source entry layout sliceFor rfl rfl fixedData
  have arrays := initialized_arrays entry layout valid mapped keyFor sliceFor fixed' prefix'
  have small : layout.count < 2 ^ 64 := by have := count_small layout valid; omega
  obtain ⟨post, root, bodyRun, rootMapped, rootWord, represented, controls, lower, upper,publicMemory⟩ :=
    helper_built_public entry layout valid keyFor sliceFor (ordinals layout.count) (ordinals_length _)
      (ordinal_inside layout.count small) mapped arrays.1 arrays.2 table count fixed'.header
      (by change 1028 * layout.count ≤ source.clock - 1; omega)
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      helperArguments = some (BuildEntry.values layout.table (BitVec.ofNat 64 layout.count)) := by
    simp [helperArguments, localVar, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact,
      BuildEntry.values, tableLocal, countLocal]
  have callRun := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "solver_radix_index")
    helperArguments (BuildEntry.values layout.table (BitVec.ofNat 64 layout.count)) BuildProgram.body callee .one
    (.val (.word 0#64)) post args lookup (by omega) bodyRun (by simp [shapeEqHOL, shapeOfHOLExact])
  let target := { post with locals := source.locals }
  refine ⟨target, root, callRun, rfl, rootMapped, rootWord, ?_, controls.trans rfl, ?_, ?_,publicMemory⟩
  · exact QueryMemory.represents_of_fields post target rfl rfl rfl _ _ _ _ _ represented
  · change source.clock - (1028 * layout.count + 1) ≤ post.clock
    change source.clock - 1 - 1028 * layout.count ≤ post.clock at lower
    omega
  · change post.clock ≤ source.clock
    change post.clock ≤ source.clock - 1 at upper
    omega

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.helper_call_public
