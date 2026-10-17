import InitECandidate.Solver.WitnessRadix.ConstructorPopulate
import InitECandidate.Solver.WitnessRadix.ConstructorPreparedContext
import InitECandidate.Solver.WitnessRadix.ConstructorPrepareFramed

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact BackingLayout
open Flapjack.Basis.Pure.MlString QueryBranch

def tablePopulatePrice (maximum : Nat) (plan : AllocatedLayout.Plan) : Nat := TableNew.price plan.capacity+1+populatePrice maximum plan.count

/-- Actual table allocation/clearing/header initialization, array-entry scopes,
complete hash/record loop, radix construction and table return. All memory and
code premises are allocated-buffer/decoded-record/ABI facts, not executions. -/
theorem table_populate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain) (shape : plan.capacity=4 ∨ plan.capacity%8=0)
    (capLocal : source.locals.lookup (ofString "cap")=some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 plan.table))))
    (tableCode : source.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one))
    (allocCode : source.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (sliceFor : BitVec 64 → Graph.Slice) (stp padScratch hashScratch : BitVec 64) (maximum : Nat)
    (recordsLocal : source.locals.lookup (ofString "slice_arr")=some (.val (.word (AllocatedLayout.layout plan).records)))
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 plan.count))))
    (pointers : ∀ index<plan.count,source.memory (cell (AllocatedLayout.layout plan) .records (16*index))=.word (sliceFor (BitVec.ofNat 64 index)).1)
    (lengths : ∀ index<plan.count,source.memory (cell (AllocatedLayout.layout plan) .records (16*index+8))=.word (sliceFor (BitVec.ofNat 64 index)).2)
    (environment : Keccak256.Environment source stp padScratch)
    (global : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hashScratch)))
    (hashCode : source.code.lookup (ofString "keccak256")=some (Keccak256.formals,Keccak256.body,.one))
    (helperCode : source.code.lookup (ofString "solver_radix_index")=some (BuildEntry.formals,BuildProgram.body,.one))
    (buffers : ∀ index<plan.count,Keccak256.Buffers stp (sliceFor (BitVec.ofNat 64 index)).1 padScratch hashScratch (sliceFor (BitVec.ofNat 64 index)).2.toNat)
    (before : stp.toNat+200≤plan.records ∧ padScratch.toNat+136≤plan.records ∧ hashScratch.toNat+32≤plan.records)
    (scratchAligned : hashScratch.toNat%8=0) (little : source.be=false)
    (lengthBound : ∀ index<plan.count,(sliceFor (BitVec.ofNat 64 index)).2.toNat≤maximum)
    (enough : tablePopulatePrice maximum plan≤source.clock) :
    ∃ keyFor : BitVec 64 → ByteKeys.Key,∃ target : PanSemStateFiniteExact 64 Guest.HostMemory,∃ root : BitVec 64,
      evaluateHOLFiniteState source (.decCall (ofString "t") .one (ofString "htab_new") [.const 32#64,localVar "cap"] tableTail)=
        (some (.returned (.val (.word (AllocatedLayout.layout plan).table))),target) ∧
      target.memaddrs (cell (AllocatedLayout.layout plan) .header 24) ∧ target.memory (cell (AllocatedLayout.layout plan) .header 24)=.word root ∧
      QueryMemory.Represents target (AllocatedLayout.layout plan).table (AllocatedLayout.layout plan).keys (AllocatedLayout.layout plan).vals root
        (initialTree keyFor sliceFor (ordinals plan.count)) ∧
      KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl (preparedState source plan) ∧ target.clock≤source.clock ∧
      source.clock-tablePopulatePrice maximum plan≤target.clock := by
  classical
  let layout := AllocatedLayout.layout plan
  let entered := preparedState source plan
  let emptyKeys : BitVec 64 → ByteKeys.Key := fun _ _ => 0#8
  obtain ⟨restoreStack,restoreFrame,prepareRun⟩ := prepare_execute_framed source plan ready domain shape capLocal heapGlobal tableCode allocCode
    environment.zeroCode (by unfold tablePopulatePrice at enough; omega)
  obtain ⟨fixedData,mapped,emptyPrefix,locals,nLocal,tLocal,entryClock⟩ := prepare_data source plan ready domain emptyKeys sliceFor recordsLocal countLocal pointers lengths
  have context := prepared_hash_context source plan ready sliceFor stp padScratch hashScratch maximum environment global hashCode buffers before scratchAligned little lengthBound
  have helper : entered.code.lookup (ofString "solver_radix_index")=some (BuildEntry.formals,BuildProgram.body,.one) := helperCode
  obtain ⟨keys,filled,root,run,rootMapped,rootWord,represented,control,upper,lower⟩ := populate entered layout (AllocatedLayout.valid plan ready) sliceFor stp padScratch hashScratch maximum
    mapped locals nLocal tLocal fixedData context helper (by change populatePrice maximum plan.count≤entered.clock; rw [entryClock]; unfold tablePopulatePrice at enough; omega)
  let target := restore source "t" (restoreStack filled)
  have frame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite filled := restoreFrame filled
  have memory : target.memory=filled.memory := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) frame
    exact h
  have domains : target.memaddrs=filled.memaddrs := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) frame
    exact h
  have endian : target.be=filled.be := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) frame
    exact h
  have clock : target.clock=filled.clock := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.clock) frame
    exact h
  refine ⟨keys,target,root,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [prepareRun,run]
  · rw [domains]; exact rootMapped
  · rw [memory]; exact rootWord
  · exact QueryMemory.represents_of_fields filled target memory.symm domains.symm endian.symm _ _ _ _ _ represented
  · have h := congrArg KeccakAbsorb.hashControl frame
    have restored : KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl filled := by
      simpa only [KeccakAbsorb.hashControl_empty] using h
    exact restored.trans control
  · rw [clock]
    rw [entryClock] at upper
    omega
  · rw [clock]
    change entered.clock-populatePrice maximum plan.count≤filled.clock at lower
    rw [entryClock] at lower
    unfold tablePopulatePrice at enough ⊢
    omega

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.table_populate
