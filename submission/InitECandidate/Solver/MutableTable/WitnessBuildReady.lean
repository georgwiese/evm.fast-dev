import InitECandidate.Solver.MutableTable.WitnessDecodedBudget
import InitECandidate.Solver.Input.ClockCost

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Current physical records, allocation room and original constructor
runtime. These are entry facts, without clock funding or future outcomes. -/
structure Ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (records table count maximum : Nat)
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64) : Prop where
  recordsLower : 2701131776≤records
  recordsBefore : records+16*count≤table
  recordsAligned : records%8=0
  tableAligned : table%8=0
  room : table+72+57*(4*count+4)+7≤33806089496
  recordsLocal : source.locals.lookup (ofString "slice_arr")=some (.val (.word (BitVec.ofNat 64 records)))
  countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))
  heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 table)))
  tableCode : source.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one)
  allocCode : source.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one)
  rows : Records source (Constructor.allocationPlan records table count 4) slices
  context : Context source (Constructor.allocationPlan records table count 4) slices stp pad scratch maximum

theorem Ready.with_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (records table count maximum : Nat)
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64) (actual : Ready source records table count maximum slices stp pad scratch) (clock : Nat) :
    Ready {source with clock:=clock} records table count maximum slices stp pad scratch :=
  ⟨actual.recordsLower,actual.recordsBefore,actual.recordsAligned,actual.tableAligned,actual.room,actual.recordsLocal,actual.countLocal,actual.heap,
    actual.tableCode,actual.allocCode,⟨actual.rows.pointers,actual.rows.lengths⟩,
    actual.context.of_control source _ (Constructor.allocationPlan records table count 4) slices stp pad scratch maximum (KeccakAbsorb.hashControl_clock source clock)⟩

/-- The completed original variable constructor contract, with current
entry metadata bundled so reached callers can derive it once. -/
theorem Ready.execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (records table count maximum : Nat)
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64) (actual : Ready source records table count maximum slices stp pad scratch)
    (enough : wholeVariablePrice slices count≤source.clock) :
    ∃ bits nextCount input logical target,
      let plan:=Constructor.allocationPlan records table count (2^bits)
      2≤bits ∧ bits≤32 ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 table)))),target) ∧
      Layout32.Built bits target plan scratch nextCount input logical ∧ History plan input ∧ input.length=count ∧ Records target plan slices ∧
      KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl {source with
        globals:=source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (table+72+57*(2^bits)+Constructor.padding (2^bits)))))} ∧
      target.clock≤source.clock ∧ source.clock-wholeVariablePrice slices count≤target.clock ∧
      2^bits≤4*count+4 ∧ (∀ query,Keccak256.Protected stp pad scratch query→query.toNat<table→target.memory query=source.memory query) ∧
      AllocatedLayout.Ready plan := by
  exact execute_variable source records table count maximum actual.recordsLower actual.recordsBefore actual.recordsAligned actual.tableAligned actual.room
    actual.recordsLocal actual.countLocal actual.heap actual.tableCode actual.allocCode slices stp pad scratch
    (fun index inside=>by simpa only [recordCell,Constructor.allocationPlan,Nat.add_zero] using actual.rows.pointers index inside)
    (fun index inside=>actual.rows.lengths index inside) actual.context.environment actual.context.global actual.context.keccakCode actual.context.hashCode actual.context.copyCode
    actual.context.insertCode actual.context.memeqCode actual.context.findCode actual.context.setCode actual.context.buffers actual.context.before actual.context.aligned actual.context.little actual.context.lengthBound enough

end InitECandidate.Solver.MutableTable.WitnessBuild
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Ready.with_clock
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Ready.execute
