import InitECandidate.Solver.MutableTable.WitnessBuildRadixLoopFramed
import InitECandidate.Solver.MutableTable.WitnessBuildRadixFinish
import InitECandidate.Solver.WitnessRadix.AllocatedPublicFrame
import InitECandidate.Solver.WitnessRadix.ConstructorPopulate

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Preserve each program's own safe words through both full record loops,
the radix helper and both table returns. The observed dictionary is common;
public memory and all FFI events agree through the entire population phase. -/
theorem paired_populate_framed (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan)
    (bits maximum : Nat) (smallBits : bits < 64) (power : plan.capacity = 2^bits)
    (sliceFor : BitVec 64 → Graph.Slice) (stp pad scratch : BitVec 64)
    (built : Layout32.Built bits source plan scratch 0 [] (fun _ => none))
    (leftLocals : Locals source plan 0) (records : Records source plan (fun i => sliceFor (BitVec.ofNat 64 i)))
    (mapped : BackingLayout.Mapped right (AllocatedLayout.layout plan))
    (rightLocals : Constructor.Locals right (AllocatedLayout.layout plan).keys (AllocatedLayout.layout plan).vals
      (AllocatedLayout.layout plan).primary (AllocatedLayout.layout plan).records 0#64)
    (rightCount : right.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 plan.count))))
    (rightTable : right.locals.lookup (ofString "t") = some (.val (.word (BitVec.ofNat 64 plan.table))))
    (fixedData : Constructor.FixedData right (AllocatedLayout.layout plan) sliceFor)
    (leftContext : Context source plan (fun i => sliceFor (BitVec.ofNat 64 i)) stp pad scratch maximum)
    (rightContext : Constructor.HashContext right (AllocatedLayout.layout plan) sliceFor stp pad scratch maximum)
    (helperCode : right.code.lookup (ofString "solver_radix_index") = some (BuildEntry.formals, BuildProgram.body, .one))
    (ffi : source.ffi = right.ffi) (region : BitVec 64 → Prop)
    (same : MemoryRegion.Agree region source.memory right.memory)
    (buffers : ∀ i < plan.count, Keccak256.BufferRegion region stp (sliceFor (BitVec.ofNat 64 i)).1 pad scratch
      (sliceFor (BitVec.ofNat 64 i)).2.toNat)
    (before : ∀ query, region query → query.toNat < plan.table)
    (safe : BitVec 64 → Prop)
    (safeBefore : ∀ query,safe query → query.toNat<plan.table)
    (safeProtected : ∀ query,safe query → Keccak256.Protected stp pad scratch query)
    (leftClock : (recordPrice maximum plan.count + 1) * plan.count ≤ source.clock)
    (rightClock : Constructor.populatePrice maximum plan.count ≤ right.clock) :
    ∃ finalCount input logical keyFor leftTarget rightTarget root,
      evaluateHOLFiniteState source (.seq recordLoop (.return (localVar "t"))) =
        (some (.returned (.val (.word (BitVec.ofNat 64 plan.table)))), leftTarget) ∧
      evaluateHOLFiniteState right (.seq Constructor.recordLoop Constructor.afterRecords) =
        (some (.returned (.val (.word (BitVec.ofNat 64 plan.table)))), rightTarget) ∧
      Layout32.Built bits leftTarget plan scratch finalCount input logical ∧ History plan input ∧
      KeysMatch plan keyFor input ∧ input.length = plan.count ∧
      Records leftTarget plan (fun i => sliceFor (BitVec.ofNat 64 i)) ∧
      rightTarget.memaddrs (BackingLayout.cell (AllocatedLayout.layout plan) .header 24) ∧
      rightTarget.memory (BackingLayout.cell (AllocatedLayout.layout plan) .header 24) = .word root ∧
      QueryMemory.Represents rightTarget (AllocatedLayout.layout plan).table (AllocatedLayout.layout plan).keys
        (AllocatedLayout.layout plan).vals root
        (BackingLayout.initialTree keyFor sliceFor (BackingLayout.ordinals plan.count)) ∧
      KeccakAbsorb.hashControl leftTarget = KeccakAbsorb.hashControl source ∧
      KeccakAbsorb.hashControl rightTarget = KeccakAbsorb.hashControl right ∧
      leftTarget.clock ≤ source.clock ∧ source.clock - (recordPrice maximum plan.count + 1) * plan.count ≤ leftTarget.clock ∧
      rightTarget.clock ≤ right.clock ∧ right.clock - Constructor.populatePrice maximum plan.count ≤ rightTarget.clock ∧
      leftTarget.ffi = rightTarget.ffi ∧ MemoryRegion.Agree region leftTarget.memory rightTarget.memory ∧
      (∀ query,safe query → leftTarget.memory query=source.memory query) ∧
      (∀ query,safe query → rightTarget.memory query=right.memory query) := by
  classical
  let layout := AllocatedLayout.layout plan
  have valid := AllocatedLayout.valid plan ready
  let emptyKeys : BitVec 64 → ByteKeys.Key := fun _ _ => 0#8
  obtain ⟨finalCount, input, logical, keyFor, leftLoop, rightLoop, leftLoopRun, rightLoopRun,
    loopBuilt, loopHistory, loopMatching, loopLength, loopPrefix, loopLeftLocals, loopRecords,
    loopFixed, loopMapped, loopRightLocals, leftLoopControl, rightLoopControl,
    leftUpper, leftLower, rightUpper, rightLower, loopFfi, loopMemory, leftOther, rightOther,leftSaved,rightSaved⟩ :=
    paired_record_loop_framed source right plan ready layout valid rfl sliceFor stp pad scratch bits maximum 0 plan.count 0 smallBits power
      [] (fun _ => none) emptyKeys (by omega) rfl built .empty (KeysMatch.empty plan emptyKeys) leftLocals records
      mapped rightLocals rightCount (Constructor.prefix_empty right layout emptyKeys) fixedData leftContext rightContext
      ffi region same buffers before
      (by intro query inside i active; exact AllocatedLayout.constructor_before plan ready query (before query inside) i)
      safe safeBefore
      (by intro query saved i active;exact AllocatedLayout.constructor_before plan ready query (safeBefore query saved) i)
      safeProtected leftClock (by unfold Constructor.populatePrice at rightClock; omega)
  have loopTable := (rightOther (ofString "t") (by decide)).trans rightTable
  have loopCount := (rightOther (ofString "n") (by decide)).trans rightCount
  have loopCode : rightLoop.code.lookup (ofString "solver_radix_index") = some (BuildEntry.formals, BuildProgram.body, .one) :=
    (congrArg (fun state => state.code.lookup (ofString "solver_radix_index")) rightLoopControl).trans helperCode
  obtain ⟨rightTarget, root, leftReturn, rightFinish, finalBuilt, rootMapped, rootWord, represented,
    finishControl, finishUpper, finishLower, finalFfi, finalMemory⟩ :=
    paired_finish leftLoop rightLoop plan layout valid bits finalCount scratch input logical loopBuilt loopLeftLocals.table
      loopMapped keyFor sliceFor loopFixed loopPrefix loopTable loopCount loopCode loopFfi region loopMemory
      (by intro query inside; exact AllocatedLayout.public_before plan ready query (before query inside))
      (by change 1028 * plan.count + 1 ≤ rightLoop.clock; unfold Constructor.populatePrice at rightClock; omega)
  obtain ⟨again,againRoot,againRun,_,_,_,_,_,_,finishMemory⟩:=Constructor.finish_public rightLoop layout valid loopMapped keyFor sliceFor
    loopFixed loopPrefix loopTable loopCount loopCode
    (by change 1028*plan.count+1≤rightLoop.clock;unfold Constructor.populatePrice at rightClock;omega)
  have againEq : again=rightTarget:=congrArg Prod.snd (againRun.symm.trans rightFinish)
  rw [againEq] at finishMemory
  let leftTarget := emptyLocalsHOLFinite leftLoop
  have finalRecords : Records leftTarget plan (fun i => sliceFor (BitVec.ofNat 64 i)) :=
    ⟨loopRecords.pointers, loopRecords.lengths⟩
  refine ⟨finalCount, input, logical, keyFor, leftTarget, rightTarget, root, ?_, ?_, finalBuilt,
    loopHistory, loopMatching, loopLength, finalRecords, rootMapped, rootWord, represented,
    (KeccakAbsorb.hashControl_empty leftLoop).trans leftLoopControl, finishControl.trans rightLoopControl,
    leftUpper, leftLower, ?_, ?_, finalFfi, finalMemory,leftSaved,?_⟩
  · exact (StateSteps.next_sequence source leftLoop _ _ leftLoopRun leftUpper).trans leftReturn
  · exact (StateSteps.next_sequence right rightLoop _ _ rightLoopRun rightUpper).trans rightFinish
  · omega
  · change rightLoop.clock - (1028 * plan.count + 1) ≤ rightTarget.clock at finishLower
    unfold Constructor.populatePrice
    omega
  · intro query saved
    exact (finishMemory query (AllocatedLayout.public_before plan ready query (safeBefore query saved))).trans (rightSaved query saved)

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.paired_populate_framed
