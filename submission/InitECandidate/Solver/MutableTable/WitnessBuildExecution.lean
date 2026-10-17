import InitECandidate.Solver.MutableTable.WitnessBuildPopulate
import InitECandidate.Solver.MutableTable.WitnessBuildCapacity
import InitECandidate.Solver.WitnessAllocationPlan

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def wholePrice (maximum count : Nat) : Nat:=(recordPrice maximum count+1)*count+4*count+46

/-- Entire actual original nodedb_build: capacity loop, real allocation and
clearing, complete hash/set loop, table return and every lexical scope.
Decoded records, buffer ownership, code and sufficient clocks remain entry
premises for the whole-guest connection. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (records table count maximum : Nat)
    (recordsLower : 2701131776≤records) (recordsBefore : records+16*count≤table)
    (recordsAligned : records%8=0) (tableAligned : table%8=0)
    (room : table+72+57*(4*count+4)+7≤33806089496)
    (recordsLocal : source.locals.lookup (ofString "slice_arr")=some (.val (.word (BitVec.ofNat 64 records))))
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 table))))
    (tableCode : source.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one))
    (allocCode : source.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64)
    (pointers : ∀ i<count,source.memory (BitVec.ofNat 64 (records+16*i))=.word (slices i).1)
    (lengths : ∀ i<count,source.memory (BitVec.ofNat 64 (records+16*i+8))=.word (slices i).2)
    (environment : Keccak256.Environment source stp pad)
    (global : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word scratch)))
    (keccakCode : source.code.lookup (ofString "keccak256")=some (Keccak256.formals,Keccak256.body,.one))
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (copyCode : source.code.lookup (ofString "memcpy")=some (Copy32.formals,Copy32.body,.one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw")=some (TableCall.formals,Insert.body,.one))
    (memeqCode : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (findCode : source.code.lookup (ofString "htab_find_slot")=some (Find.formals,Find.body,.one))
    (setCode : source.code.lookup (ofString "htab_set")=some (TableCall.formals,Set.body,.one))
    (buffers : ∀ i<count,Keccak256.Buffers stp (slices i).1 pad scratch (slices i).2.toNat)
    (before : stp.toNat+200≤records ∧ pad.toNat+136≤records ∧ scratch.toNat+32≤records)
    (aligned : scratch.toNat%8=0) (little : source.be=false)
    (lengthBound : ∀ i<count,(slices i).2.toNat≤maximum) (enough : wholePrice maximum count≤source.clock) :
    ∃ bits nextCount input logical target,
      let plan:=Constructor.allocationPlan records table count (2^bits)
      2≤bits ∧ bits≤32 ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 table)))),target) ∧
      Layout32.Built bits target plan scratch nextCount input logical ∧ History plan input ∧ input.length=count ∧ Records target plan slices ∧
      KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl {source with
        globals:=source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (table+72+57*(2^bits)+Constructor.padding (2^bits)))))} ∧
      target.clock≤source.clock ∧ source.clock-wholePrice maximum count≤target.clock := by
  have small:=Capacity.count_small_of_records records table count recordsLower recordsBefore (by omega)
  obtain ⟨capped,paid,bits,capRun,paidBound,lower,upper,sufficient,capBound,capLocal,capFrame,capOther⟩:=
    capacity_entry source count small countLocal (by unfold wholePrice at enough;omega)
  let plan:=Constructor.allocationPlan records table count (2^bits)
  have shape:=Capacity.power_shape bits lower
  have ready : AllocatedLayout.Ready plan:=Constructor.allocation_ready records table count (2^bits) recordsLower recordsBefore recordsAligned tableAligned room sufficient capBound shape
  have capClock : capped.clock=source.clock-paid:=congrArg (fun state=>state.clock) capFrame
  have capMemory : capped.memory=source.memory:=congrArg (fun state=>state.memory) capFrame
  have capCodes : capped.code=source.code:=congrArg (fun state=>state.code) capFrame
  have capGlobals : capped.globals=source.globals:=congrArg (fun state=>state.globals) capFrame
  have capControl : KeccakAbsorb.hashControl capped=KeccakAbsorb.hashControl source := by
    have unchanged:=congrArg KeccakAbsorb.hashControl capFrame
    simpa only [KeccakAbsorb.hashControl_empty,KeccakAbsorb.hashControl_clock] using unchanged
  have capEnvironment:=Keccak256.Environment.of_control source capped stp pad capControl environment
  have capRecords : Records capped plan slices := by
    constructor
    · intro i inside
      rw [capMemory]
      exact pointers i inside
    · intro i inside
      rw [capMemory]
      exact lengths i inside
  have capContext : Context capped plan slices stp pad scratch maximum := by
    refine ⟨?_,?_,capEnvironment,buffers,before,aligned,?_,?_,?_,?_,?_,?_,?_,lengthBound⟩
    · rw [capGlobals];exact global
    · rw [capCodes];exact keccakCode
    · have endian : capped.be=source.be:=congrArg (fun state=>state.be) capFrame
      exact endian.trans little
    · rw [capCodes];exact hashCode
    · rw [capCodes];exact copyCode
    · rw [capCodes];exact insertCode
    · rw [capCodes];exact memeqCode
    · rw [capCodes];exact findCode
    · rw [capCodes];exact setCode
  have priceBound : tablePopulatePrice maximum plan+30≤wholePrice maximum count := by
    have tablePrice:=Constructor.table_price_bound (2^bits)
    unfold tablePopulatePrice wholePrice
    change TableNew.price (2^bits)+1+(recordPrice maximum count+1)*count+30≤(recordPrice maximum count+1)*count+4*count+46
    omega
  obtain ⟨nextCount,input,logical,filled,tableRun,built,history,length,finalRecords,control,tableUpper,tableLower⟩:=table_populate capped plan ready bits (by omega) rfl shape capLocal
    (by rw [capGlobals];exact heapGlobal) (by rw [capCodes];exact tableCode) (by rw [capCodes];exact allocCode) scratch stp pad slices maximum
    ((capOther (ofString "slice_arr") (by decide)).trans recordsLocal) ((capOther (ofString "n") (by decide)).trans countLocal)
    capRecords capContext (by rw [capClock];omega)
  change evaluateHOLFiniteState capped allocatedTail=(some (.returned (.val (.word (BitVec.ofNat 64 table)))),filled) at tableRun
  let target:=restore source "cap" filled
  have nextBuilt:=Layout32.built_fields filled target plan bits scratch nextCount input logical rfl rfl rfl built
  have recordsResult:=Records.of_earlier filled target plan ready slices (by intros;rfl) finalRecords
  refine ⟨bits,nextCount,input,logical,target,lower,upper,?_,nextBuilt,history,length,recordsResult,?_,?_,?_⟩
  · rw [capRun,tableRun]
  · have initialControl : KeccakAbsorb.hashControl (prepared capped plan)=KeccakAbsorb.hashControl {source with
        globals:=source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (table+72+57*(2^bits)+Constructor.padding (2^bits)))))} := by
      have updated:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with
        globals:=state.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (table+72+57*(2^bits)+Constructor.padding (2^bits)))))}) capControl
      exact updated
    exact control.trans initialControl
  · change filled.clock≤source.clock
    rw [capClock] at tableUpper
    omega
  · change source.clock-wholePrice maximum count≤filled.clock
    rw [capClock] at tableLower
    omega

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.execute
