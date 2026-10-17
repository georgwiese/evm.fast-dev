import InitECandidate.Solver.WitnessRadix.ConstructorPlan

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact BackingLayout
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Entire literal candidate nodedb_build, including capacity selection, all
allocations/clearing, real hashing/copying, radix construction and scopes.
Decoded/allocated entry facts remain explicit for the whole-guest proof. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (records table count maximum : Nat)
    (recordsLower : 2701131776≤records) (recordsBefore : records+16*count≤table)
    (recordsAligned : records%8=0) (tableAligned : table%8=0)
    (room : table+72+57*(4*count+4)+7≤33806089496)
    (recordsLocal : source.locals.lookup (ofString "slice_arr")=some (.val (.word (BitVec.ofNat 64 records))))
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 table))))
    (tableCode : source.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one))
    (allocCode : source.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (sliceFor : BitVec 64 → Graph.Slice) (stp padScratch hashScratch : BitVec 64)
    (pointers : ∀ index<count,source.memory (byteAddress (BitVec.ofNat 64 records) (16*index))=.word (sliceFor (BitVec.ofNat 64 index)).1)
    (lengths : ∀ index<count,source.memory (byteAddress (BitVec.ofNat 64 records) (16*index+8))=.word (sliceFor (BitVec.ofNat 64 index)).2)
    (environment : Keccak256.Environment source stp padScratch)
    (global : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hashScratch)))
    (hashCode : source.code.lookup (ofString "keccak256")=some (Keccak256.formals,Keccak256.body,.one))
    (helperCode : source.code.lookup (ofString "solver_radix_index")=some (BuildEntry.formals,BuildProgram.body,.one))
    (buffers : ∀ index<count,Keccak256.Buffers stp (sliceFor (BitVec.ofNat 64 index)).1 padScratch hashScratch (sliceFor (BitVec.ofNat 64 index)).2.toNat)
    (before : stp.toNat+200≤records ∧ padScratch.toNat+136≤records ∧ hashScratch.toNat+32≤records)
    (scratchAligned : hashScratch.toNat%8=0) (little : source.be=false)
    (lengthBound : ∀ index<count,(sliceFor (BitVec.ofNat 64 index)).2.toNat≤maximum)
    (enough : wholePrice maximum count≤source.clock) :
    ∃ capacity : Nat,∃ keyFor : BitVec 64 → ByteKeys.Key,∃ target : PanSemStateFiniteExact 64 Guest.HostMemory,∃ root : BitVec 64,
      let plan := allocationPlan records table count capacity
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 table)))),target) ∧
      target.memaddrs (cell (AllocatedLayout.layout plan) .header 24) ∧ target.memory (cell (AllocatedLayout.layout plan) .header 24)=.word root ∧
      QueryMemory.Represents target (AllocatedLayout.layout plan).table (AllocatedLayout.layout plan).keys (AllocatedLayout.layout plan).vals root
        (initialTree keyFor sliceFor (ordinals count)) ∧
      KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl {source with
        globals := source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (table+72+57*capacity+padding capacity))))} ∧
      target.clock≤source.clock ∧ source.clock-wholePrice maximum count≤target.clock := by
  classical
  have small := Capacity.count_small_of_records records table count recordsLower recordsBefore (by omega)
  obtain ⟨capped,paid,capacity,capRun,paidBound,sufficient,capBound,capTop,shape,capLocal,capFrame,capOther⟩ :=
    capacity_entry source count small countLocal (by unfold wholePrice at enough; omega)
  let plan := allocationPlan records table count capacity
  have ready : AllocatedLayout.Ready plan := allocation_ready records table count capacity recordsLower recordsBefore recordsAligned tableAligned room sufficient capBound shape
  have capClock : capped.clock=source.clock-paid := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.clock) capFrame
    exact h
  have capMemory : capped.memory=source.memory := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) capFrame
    exact h
  have capCodes : capped.code=source.code := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) capFrame
    exact h
  have capGlobals : capped.globals=source.globals := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) capFrame
    exact h
  have capControl : KeccakAbsorb.hashControl capped=KeccakAbsorb.hashControl source := by
    have h := congrArg KeccakAbsorb.hashControl capFrame
    simpa only [KeccakAbsorb.hashControl_empty,KeccakAbsorb.hashControl_clock] using h
  have capEnvironment := Keccak256.Environment.of_control source capped stp padScratch capControl environment
  have capRecordLocal : capped.locals.lookup (ofString "slice_arr")=some (.val (.word (AllocatedLayout.layout plan).records)) :=
    (capOther (ofString "slice_arr") (by decide)).trans recordsLocal
  have capCountLocal : capped.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 plan.count))) :=
    (capOther (ofString "n") (by decide)).trans countLocal
  have capHeap : capped.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 plan.table))) := by rw [capGlobals]; exact heapGlobal
  have capTableCode : capped.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one) := by rw [capCodes]; exact tableCode
  have capAllocCode : capped.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one) := by rw [capCodes]; exact allocCode
  have capGlobal : capped.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hashScratch)) := by rw [capGlobals]; exact global
  have capHashCode : capped.code.lookup (ofString "keccak256")=some (Keccak256.formals,Keccak256.body,.one) := by rw [capCodes]; exact hashCode
  have capHelperCode : capped.code.lookup (ofString "solver_radix_index")=some (BuildEntry.formals,BuildProgram.body,.one) := by rw [capCodes]; exact helperCode
  have capPointers : ∀ index<plan.count,capped.memory (cell (AllocatedLayout.layout plan) .records (16*index))=.word (sliceFor (BitVec.ofNat 64 index)).1 := by
    intro index inside
    rw [capMemory]
    exact pointers index inside
  have capLengths : ∀ index<plan.count,capped.memory (cell (AllocatedLayout.layout plan) .records (16*index+8))=.word (sliceFor (BitVec.ofNat 64 index)).2 := by
    intro index inside
    rw [capMemory]
    exact lengths index inside
  have capLittle : capped.be=false := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) capControl
    exact h.trans little
  have priceBound : tablePopulatePrice maximum plan+30≤wholePrice maximum count :=
    table_populate_price_bound maximum records table count capacity capBound
  obtain ⟨keys,filled,root,tableRun,rootMapped,rootWord,represented,tableControl,tableUpper,tableLower⟩ :=
    table_populate capped plan ready capEnvironment.domain shape capLocal capHeap capTableCode capAllocCode sliceFor stp padScratch hashScratch maximum
      capRecordLocal capCountLocal capPointers capLengths capEnvironment capGlobal capHashCode capHelperCode buffers before scratchAligned capLittle lengthBound
      (by rw [capClock]; omega)
  change evaluateHOLFiniteState capped allocatedTail=(some (.returned (.val (.word (BitVec.ofNat 64 table)))),filled) at tableRun
  let target := restore source "cap" filled
  refine ⟨capacity,keys,target,root,?_,rootMapped,rootWord,?_,?_,?_,?_⟩
  · rw [capRun,tableRun]
  · exact QueryMemory.represents_of_fields filled target rfl rfl rfl _ _ _ _ _ represented
  · have initialControl : KeccakAbsorb.hashControl (preparedState capped plan)=KeccakAbsorb.hashControl {source with
        globals := source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (table+72+57*capacity+padding capacity))))} := by
      have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with
        globals := state.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (table+72+57*capacity+padding capacity))))}) capControl
      exact h
    exact (KeccakAbsorb.hashControl_restore source filled "cap").trans (tableControl.trans initialControl)
  · change filled.clock≤source.clock
    rw [capClock] at tableUpper
    omega
  · change source.clock-wholePrice maximum count≤filled.clock
    rw [capClock] at tableLower
    omega

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.execute
