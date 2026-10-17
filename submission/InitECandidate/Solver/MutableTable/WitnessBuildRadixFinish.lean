import InitECandidate.Solver.MutableTable.WitnessBuildRadixLoop
import InitECandidate.Solver.WitnessRadix.ConstructorFinishPublic

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The original table return and complete radix index-build/return preserve
the synchronized public memory and FFI relation. The original physical table
invariant survives its return; the radix result represents the observed keys. -/
theorem paired_finish (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (plan : AllocatedLayout.Plan) (layout : BackingLayout.Layout) (valid : BackingLayout.Valid layout)
    (bits count : Nat) (scratch : BitVec 64) (input : List (Find.Key32 × BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (built : Layout32.Built bits source plan scratch count input logical)
    (leftTable : source.locals.lookup (ofString "t") = some (.val (.word (BitVec.ofNat 64 plan.table))))
    (mapped : BackingLayout.Mapped right layout) (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (fixedData : Constructor.FixedData right layout sliceFor)
    (prefixData : Constructor.Prefix right layout keyFor layout.count)
    (rightTable : right.locals.lookup (ofString "t") = some (.val (.word layout.table)))
    (rightCount : right.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 layout.count))))
    (code : right.code.lookup (ofString "solver_radix_index") = some (BuildEntry.formals, BuildProgram.body, .one))
    (ffi : source.ffi = right.ffi) (region : BitVec 64 → Prop)
    (same : MemoryRegion.Agree region source.memory right.memory)
    (outside : ∀ query, region query → BackingLayout.PublicWord layout query)
    (enough : 1028 * layout.count + 1 ≤ right.clock) :
    ∃ rightTarget root,
      evaluateHOLFiniteState source (.return (localVar "t")) =
        (some (.returned (.val (.word (BitVec.ofNat 64 plan.table)))), emptyLocalsHOLFinite source) ∧
      evaluateHOLFiniteState right Constructor.afterRecords =
        (some (.returned (.val (.word layout.table))), rightTarget) ∧
      Layout32.Built bits (emptyLocalsHOLFinite source) plan scratch count input logical ∧
      rightTarget.memaddrs (BackingLayout.cell layout .header 24) ∧
      rightTarget.memory (BackingLayout.cell layout .header 24) = .word root ∧
      QueryMemory.Represents rightTarget layout.table layout.keys layout.vals root
        (BackingLayout.initialTree keyFor sliceFor (BackingLayout.ordinals layout.count)) ∧
      KeccakAbsorb.hashControl rightTarget = KeccakAbsorb.hashControl right ∧
      rightTarget.clock ≤ right.clock ∧ right.clock - (1028 * layout.count + 1) ≤ rightTarget.clock ∧
      (emptyLocalsHOLFinite source).ffi = rightTarget.ffi ∧
      MemoryRegion.Agree region (emptyLocalsHOLFinite source).memory rightTarget.memory := by
  have leftRun : evaluateHOLFiniteState source (.return (localVar "t")) =
      (some (.returned (.val (.word (BitVec.ofNat 64 plan.table)))), emptyLocalsHOLFinite source) := by
    simp [evaluateHOLFiniteState_return, localVar, evalHOLExact, toExact, leftTable,
      shapeOfHOLExact, sizeOfShapeWithContextHOL]
  obtain ⟨rightTarget, root, rightRun, rootMapped, rootWord, represented, control, lower, upper, publicMemory⟩ :=
    Constructor.finish_public right layout valid mapped keyFor sliceFor fixedData prefixData rightTable rightCount code enough
  have rightFfi : rightTarget.ffi = right.ffi := congrArg (fun state => state.ffi) control
  have hashControl := KeccakAbsorb.hashControl_of_control right rightTarget control
  have nextBuilt := Layout32.built_fields source (emptyLocalsHOLFinite source) plan bits scratch count input logical rfl rfl rfl built
  refine ⟨rightTarget, root, leftRun, rightRun, nextBuilt, rootMapped, rootWord, represented,
    hashControl, upper, lower, ffi.trans rightFfi.symm, ?_⟩
  intro query inside
  exact (same query inside).trans (publicMemory query (outside query inside)).symm

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.paired_finish
