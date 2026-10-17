import InitECandidate.Solver.MutableTable.WitnessBuildRadixExecution
import InitECandidate.Solver.MutableTable.WitnessBuildEnvironments
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Real paired constructor callers, including ignored and scoped assigned
returns. Exact globals/events/public-memory and common observed dictionaries
are retained through the actual finite ABI and arbitrary continuations. -/
theorem paired_call_execute (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (leftArguments rightArguments : List (ExpHOL 64)) (records table count maximum : Nat)
    (leftArgs : evalListHOLFinite source (h := fun q => Classical.propDecidable (source.memaddrs q)) leftArguments = some (Constructor.values records count))
    (rightArgs : evalListHOLFinite right (h := fun q => Classical.propDecidable (right.memaddrs q)) rightArguments = some (Constructor.values records count))
    (leftCode : source.code.lookup (ofString "nodedb_build") = some (Constructor.formals, body, .one))
    (rightCode : right.code.lookup (ofString "nodedb_build") = some (Constructor.formals, Constructor.body, .one))
    (recordsLower : 2701131776 ≤ records) (recordsBefore : records + 16*count ≤ table)
    (recordsAligned : records % 8 = 0) (tableAligned : table % 8 = 0)
    (room : table + 72 + 57*(4*count+4) + 7 ≤ 33806089496)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 table))))
    (leftTableCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (rightTableCode : right.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (leftAllocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (rightAllocCode : right.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (sliceFor : BitVec 64 → Graph.Slice) (stp pad scratch : BitVec 64)
    (pointers : ∀ i < count, source.memory (byteAddress (BitVec.ofNat 64 records) (16*i)) = .word (sliceFor (BitVec.ofNat 64 i)).1)
    (lengths : ∀ i < count, source.memory (byteAddress (BitVec.ofNat 64 records) (16*i+8)) = .word (sliceFor (BitVec.ofNat 64 i)).2)
    (context : ∀ capacity, Context source (Constructor.allocationPlan records table count capacity)
      (fun i => sliceFor (BitVec.ofNat 64 i)) stp pad scratch maximum)
    (rightEnvironment : Keccak256.Environment right stp pad)
    (rightHashCode : right.code.lookup (ofString "keccak256") = some (Keccak256.formals, Keccak256.body, .one))
    (helperCode : right.code.lookup (ofString "solver_radix_index") = some (BuildEntry.formals, BuildProgram.body, .one))
    (locals : source.locals = right.locals) (globals : source.globals = right.globals)
    (endian : source.be = right.be) (ffi : source.ffi = right.ffi)
    (region : BitVec 64 → Prop) (same : MemoryRegion.Agree region source.memory right.memory)
    (before : ∀ query, region query → query.toNat < table)
    (recordPublic : ∀ i < count, region (byteAddress (BitVec.ofNat 64 records) (16*i)) ∧
      region (byteAddress (BitVec.ofNat 64 records) (16*i+8)))
    (buffers : ∀ i < count, Keccak256.BufferRegion region stp (sliceFor (BitVec.ofNat 64 i)).1 pad scratch
      (sliceFor (BitVec.ofNat 64 i)).2.toNat)
    (leftClock : wholePrice maximum count + 1 ≤ source.clock)
    (rightClock : Constructor.wholePrice maximum count + 1 ≤ right.clock) :
    ∃ bits finalCount input logical keyFor leftTarget rightTarget root,
      let plan := Constructor.allocationPlan records table count (2^bits)
      2 ≤ bits ∧ bits ≤ 32 ∧ AllocatedLayout.Ready plan ∧
      evaluateHOLFiniteState source (.call (some (none,none)) (ofString "nodedb_build") leftArguments) = (none,leftTarget) ∧
      evaluateHOLFiniteState right (.call (some (none,none)) (ofString "nodedb_build") rightArguments) = (none,rightTarget) ∧
      leftTarget.locals=source.locals ∧ rightTarget.locals=right.locals ∧ leftTarget.locals=rightTarget.locals ∧
      (∀ (name : String) (continuation : ProgHOL 64),
        evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "nodedb_build") leftArguments continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite (ofString name) (.val (.word (BitVec.ofNat 64 table))) leftTarget) continuation;
            (output.1,restore source name output.2))) ∧
      (∀ (name : String) (continuation : ProgHOL 64),
        evaluateHOLFiniteState right (.decCall (ofString name) .one (ofString "nodedb_build") rightArguments continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite (ofString name) (.val (.word (BitVec.ofNat 64 table))) rightTarget) continuation;
            (output.1,restore right name output.2))) ∧
      Layout32.Built bits leftTarget plan scratch finalCount input logical ∧ History plan input ∧
      KeysMatch plan keyFor input ∧ input.length = count ∧ Records leftTarget plan (fun i => sliceFor (BitVec.ofNat 64 i)) ∧
      rightTarget.memaddrs (BackingLayout.cell (AllocatedLayout.layout plan) .header 24) ∧
      rightTarget.memory (BackingLayout.cell (AllocatedLayout.layout plan) .header 24) = .word root ∧
      QueryMemory.Represents rightTarget (AllocatedLayout.layout plan).table (AllocatedLayout.layout plan).keys
        (AllocatedLayout.layout plan).vals root
        (BackingLayout.initialTree keyFor sliceFor (BackingLayout.ordinals count)) ∧
      KeccakAbsorb.hashControl leftTarget = KeccakAbsorb.hashControl {source with
        globals := source.globals.update (ofString "heap_ptr", .val (.word
          (BitVec.ofNat 64 (table+72+57*(2^bits)+Constructor.padding (2^bits)))))} ∧
      KeccakAbsorb.hashControl rightTarget = KeccakAbsorb.hashControl {right with
        globals := right.globals.update (ofString "heap_ptr", .val (.word
          (BitVec.ofNat 64 (table+72+57*(2^bits)+Constructor.padding (2^bits)))))} ∧
      leftTarget.clock ≤ source.clock ∧ source.clock - (wholePrice maximum count + 1) ≤ leftTarget.clock ∧
      rightTarget.clock ≤ right.clock ∧ right.clock - (Constructor.wholePrice maximum count + 1) ≤ rightTarget.clock ∧
      leftTarget.globals = rightTarget.globals ∧ leftTarget.ffi = rightTarget.ffi ∧
      MemoryRegion.Agree region leftTarget.memory rightTarget.memory := by
  classical
  obtain ⟨callee,leftLookup,rightLookup,recordsLocal,countLocal⟩ := paired_environments source right records count leftCode rightCode
  let leftEntry := callEntryStateHOLFinite source callee
  let rightEntry := callEntryStateHOLFinite right callee
  have leftContext : ∀ capacity, Context leftEntry (Constructor.allocationPlan records table count capacity)
      (fun i => sliceFor (BitVec.ofNat 64 i)) stp pad scratch maximum := by
    intro capacity
    exact Context.of_control source leftEntry _ _ stp pad scratch maximum rfl (context capacity)
  have rightEntryEnvironment := Keccak256.Environment.of_control right rightEntry stp pad rfl rightEnvironment
  obtain ⟨bits,finalCount,input,logical,keyFor,leftFinished,rightFinished,root,bitsLow,bitsTop,ready,
    leftBody,rightBody,nextBuilt,nextHistory,nextMatching,nextLength,nextRecords,rootMapped,rootWord,represented,
    leftControl,rightControl,leftUpper,leftLower,rightUpper,rightLower,finalGlobals,finalFfi,finalMemory⟩ :=
    paired_execute leftEntry rightEntry records table count maximum recordsLower recordsBefore recordsAligned tableAligned room
      recordsLocal countLocal heap leftTableCode rightTableCode leftAllocCode rightAllocCode sliceFor stp pad scratch pointers lengths
      leftContext rightEntryEnvironment rightHashCode helperCode rfl globals endian ffi region same before recordPublic buffers
      (by change wholePrice maximum count ≤ source.clock-1;omega)
      (by change Constructor.wholePrice maximum count ≤ right.clock-1;omega)
  let plan := Constructor.allocationPlan records table count (2^bits)
  let leftTarget := {leftFinished with locals:=source.locals}
  let rightTarget := {rightFinished with locals:=right.locals}
  have leftCall := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "nodedb_build")
    leftArguments (Constructor.values records count) body callee .one (.val (.word (BitVec.ofNat 64 table))) leftFinished
    leftArgs leftLookup (by unfold wholePrice at leftClock;omega) leftBody (by simp [shapeEqHOL,shapeOfHOLExact])
  have rightCall := evaluateHOLFiniteState_call_return_caller_locals right none (ofString "nodedb_build")
    rightArguments (Constructor.values records count) Constructor.body callee .one (.val (.word (BitVec.ofNat 64 table))) rightFinished
    rightArgs rightLookup (by unfold Constructor.wholePrice at rightClock;omega) rightBody (by simp [shapeEqHOL,shapeOfHOLExact])
  have leftScoped (name : String) (continuation : ProgHOL 64) := Input.CallNormal.return_execute source leftFinished name .one
    (ofString "nodedb_build") leftArguments (Constructor.values records count) body continuation callee .one
    (.val (.word (BitVec.ofNat 64 table))) leftArgs leftLookup (by unfold wholePrice at leftClock;omega) leftBody
    (by simp [shapeEqHOL,shapeOfHOLExact])
  have rightScoped (name : String) (continuation : ProgHOL 64) := Input.CallNormal.return_execute right rightFinished name .one
    (ofString "nodedb_build") rightArguments (Constructor.values records count) Constructor.body continuation callee .one
    (.val (.word (BitVec.ofNat 64 table))) rightArgs rightLookup (by unfold Constructor.wholePrice at rightClock;omega) rightBody
    (by simp [shapeEqHOL,shapeOfHOLExact])
  have finalBuilt := Layout32.built_fields leftFinished leftTarget plan bits scratch finalCount input logical rfl rfl rfl nextBuilt
  have finalRecords : Records leftTarget plan (fun i => sliceFor (BitVec.ofNat 64 i)) := ⟨nextRecords.pointers,nextRecords.lengths⟩
  refine ⟨bits,finalCount,input,logical,keyFor,leftTarget,rightTarget,root,bitsLow,bitsTop,ready,leftCall,rightCall,
    rfl,rfl,locals,?_,?_,finalBuilt,nextHistory,nextMatching,nextLength,finalRecords,rootMapped,rootWord,
    QueryMemory.represents_of_fields rightFinished rightTarget rfl rfl rfl _ _ _ _ _ represented,
    leftControl,rightControl,?_,?_,?_,?_,finalGlobals,finalFfi,finalMemory⟩
  · intro name continuation
    exact leftScoped name continuation
  · intro name continuation
    exact rightScoped name continuation
  · change leftFinished.clock ≤ source.clock
    change leftFinished.clock ≤ source.clock-1 at leftUpper
    omega
  · change source.clock-(wholePrice maximum count+1) ≤ leftFinished.clock
    change source.clock-1-wholePrice maximum count ≤ leftFinished.clock at leftLower
    omega
  · change rightFinished.clock ≤ right.clock
    change rightFinished.clock ≤ right.clock-1 at rightUpper
    omega
  · change right.clock-(Constructor.wholePrice maximum count+1) ≤ rightFinished.clock
    change right.clock-1-Constructor.wholePrice maximum count ≤ rightFinished.clock at rightLower
    omega

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.paired_call_execute
