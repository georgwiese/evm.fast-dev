import InitECandidate.Solver.WitnessRadix.ConstructorExecution
import InitECandidate.Solver.WitnessRadix.ConstructorEnvironment

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact BackingLayout
open Flapjack.Basis.Pure.MlString

/-- Actual constructor caller/callee from decoded arena records and concrete
code/global facts. The call restores caller locals, advances the heap exactly
and returns the represented radix table in bounded source clocks. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (records table count maximum : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments=some (values records count))
    (code : source.code.lookup (ofString "nodedb_build")=some (formals,body,.one))
    (recordsLower : 2701131776≤records) (recordsBefore : records+16*count≤table)
    (recordsAligned : records%8=0) (tableAligned : table%8=0) (room : table+72+57*(4*count+4)+7≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 table))))
    (tableCode : source.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one))
    (allocCode : source.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (sliceFor : BitVec 64 → Graph.Slice) (stp padScratch hashScratch : BitVec 64)
    (pointers : ∀ index<count,source.memory (byteAddress (BitVec.ofNat 64 records) (16*index))=.word (sliceFor (BitVec.ofNat 64 index)).1)
    (lengths : ∀ index<count,source.memory (byteAddress (BitVec.ofNat 64 records) (16*index+8))=.word (sliceFor (BitVec.ofNat 64 index)).2)
    (hashEnvironment : Keccak256.Environment source stp padScratch)
    (global : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hashScratch)))
    (hashCode : source.code.lookup (ofString "keccak256")=some (Keccak256.formals,Keccak256.body,.one))
    (helperCode : source.code.lookup (ofString "solver_radix_index")=some (BuildEntry.formals,BuildProgram.body,.one))
    (buffers : ∀ index<count,Keccak256.Buffers stp (sliceFor (BitVec.ofNat 64 index)).1 padScratch hashScratch (sliceFor (BitVec.ofNat 64 index)).2.toNat)
    (before : stp.toNat+200≤records ∧ padScratch.toNat+136≤records ∧ hashScratch.toNat+32≤records)
    (scratchAligned : hashScratch.toNat%8=0) (little : source.be=false)
    (lengthBound : ∀ index<count,(sliceFor (BitVec.ofNat 64 index)).2.toNat≤maximum)
    (enough : wholePrice maximum count+1≤source.clock) :
    ∃ capacity : Nat,∃ keyFor : BitVec 64 → ByteKeys.Key,∃ output : PanSemStateFiniteExact 64 Guest.HostMemory,∃ root : BitVec 64,
      let plan := allocationPlan records table count capacity
      evaluateHOLFiniteState source (.call (some (none,none)) (ofString "nodedb_build") arguments)=(none,output) ∧ output.locals=source.locals ∧
      output.memaddrs (cell (AllocatedLayout.layout plan) .header 24) ∧ output.memory (cell (AllocatedLayout.layout plan) .header 24)=.word root ∧
      QueryMemory.Represents output (AllocatedLayout.layout plan).table (AllocatedLayout.layout plan).keys (AllocatedLayout.layout plan).vals root
        (initialTree keyFor sliceFor (ordinals count)) ∧
      KeccakAbsorb.hashControl output=KeccakAbsorb.hashControl {source with
        globals := source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (table+72+57*capacity+padding capacity))))} ∧
      output.clock≤source.clock ∧ source.clock-(wholePrice maximum count+1)≤output.clock := by
  classical
  obtain ⟨callee,lookup,recordsLocal,countLocal⟩ := environment source.code.lookup records count code
  let entry := callEntryStateHOLFinite source callee
  have entryEnvironment := Keccak256.Environment.of_control source entry stp padScratch rfl hashEnvironment
  obtain ⟨capacity,keys,finished,root,run,rootMapped,rootWord,represented,control,upper,lower⟩ :=
    execute entry records table count maximum recordsLower recordsBefore recordsAligned tableAligned room recordsLocal countLocal heapGlobal tableCode allocCode
      sliceFor stp padScratch hashScratch pointers lengths entryEnvironment global hashCode helperCode buffers before scratchAligned little lengthBound
      (by change wholePrice maximum count≤source.clock-1; omega)
  let output := {finished with locals := source.locals}
  have callRun := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "nodedb_build") arguments (values records count)
    body callee .one (.val (.word (BitVec.ofNat 64 table))) finished args lookup (by omega) run (by simp [shapeEqHOL,shapeOfHOLExact])
  refine ⟨capacity,keys,output,root,callRun,rfl,rootMapped,rootWord,?_,control,?_,?_⟩
  · exact QueryMemory.represents_of_fields finished output rfl rfl rfl _ _ _ _ _ represented
  · change finished.clock≤source.clock
    change finished.clock≤source.clock-1 at upper
    omega
  · change source.clock-(wholePrice maximum count+1)≤finished.clock
    change source.clock-1-wholePrice maximum count≤finished.clock at lower
    omega

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.call_execute
