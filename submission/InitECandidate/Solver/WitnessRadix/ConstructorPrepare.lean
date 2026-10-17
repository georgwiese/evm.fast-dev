import InitECandidate.Solver.WitnessRadix.ConstructorArrayEntry
import InitECandidate.Solver.WitnessRadix.TableCallData

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact BackingLayout
open Flapjack.Basis.Pure.MlString QueryBranch

def preparedState {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) : PanSemStateFiniteExact 64 F :=
  arrayEntry (TableNew.callState source "t" plan) (AllocatedLayout.layout plan)

/-- Actual htab_new caller followed by the literal three array loads and
zero ordinal declaration, exposing the real remaining record loop. -/
theorem prepare_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs = InitE.ordinaryDomain)
    (capacityShape : plan.capacity = 4 ∨ plan.capacity % 8 = 0)
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 plan.table))))
    (tableCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (enough : TableNew.price plan.capacity + 1 ≤ source.clock) :
    ∃ restoreStack : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState source (.decCall (ofString "t") .one (ofString "htab_new")
        [.const 32#64, localVar "cap"] tableTail) =
        (let output := evaluateHOLFiniteState (preparedState source plan) (.seq recordLoop afterRecords);
         (output.1, restore source "t" (restoreStack output.2))) := by
  classical
  let called := TableNew.callState source "t" plan
  let layout := AllocatedLayout.layout plan
  have header : BuildEntry.Header called layout.table layout.keys layout.vals layout.primary layout.backup :=
    TableNew.header_of_fields { source with memory := TableNew.resultMemory source.memory source.be plan }
      called _ _ _ _ _ rfl rfl (TableNew.result_header source plan ready domain)
  have tableLocal : called.locals.lookup (ofString "t") = some (.val (.word layout.table)) := bind_lookup_same _ _ _
  obtain ⟨restoreStack, setup⟩ := array_initialize called layout tableLocal header
  have prefixRun := BuildEntry.declarations_execute setup (.seq recordLoop afterRecords)
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [.const 32#64, localVar "cap"] = some (TableNew.values plan.capacity) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, TableNew.values, capLocal]
  have callRun := TableNew.call_execute source plan "t" [.const 32#64, localVar "cap"] tableTail ready domain capacityShape
    args tableCode heapGlobal allocCode zeroCode enough
  refine ⟨restoreStack, ?_⟩
  rw [callRun, table_tail_shape, prefixRun]
  rfl

/-- The actual prepared loop entry has allocated mapped arrays, decoded
record/header data, an empty initialized prefix and concrete caller locals. -/
theorem prepare_data {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs = InitE.ordinaryDomain)
    (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (recordsLocal : source.locals.lookup (ofString "slice_arr") = some (.val (.word (AllocatedLayout.layout plan).records)))
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 plan.count))))
    (pointers : ∀ index < plan.count, source.memory (cell (AllocatedLayout.layout plan) .records (16 * index)) =
      .word (sliceFor (BitVec.ofNat 64 index)).1)
    (lengths : ∀ index < plan.count, source.memory (cell (AllocatedLayout.layout plan) .records (16 * index + 8)) =
      .word (sliceFor (BitVec.ofNat 64 index)).2) :
    FixedData (preparedState source plan) (AllocatedLayout.layout plan) sliceFor ∧
      Mapped (preparedState source plan) (AllocatedLayout.layout plan) ∧
      Prefix (preparedState source plan) (AllocatedLayout.layout plan) keyFor 0 ∧
      Locals (preparedState source plan) (AllocatedLayout.layout plan).keys (AllocatedLayout.layout plan).vals
        (AllocatedLayout.layout plan).primary (AllocatedLayout.layout plan).records 0#64 ∧
      (preparedState source plan).locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 plan.count))) ∧
      (preparedState source plan).locals.lookup (ofString "t") = some (.val (.word (AllocatedLayout.layout plan).table)) ∧
      (preparedState source plan).clock = source.clock - (TableNew.price plan.capacity + 1) := by
  let called := TableNew.callState source "t" plan
  let layout := AllocatedLayout.layout plan
  have fixedData := TableNew.call_fixed_data source "t" plan ready domain sliceFor pointers lengths
  have calledRecords : called.locals.lookup (ofString "slice_arr") = some (.val (.word layout.records)) := by
    unfold called TableNew.callState
    rw [bind_lookup_other _ "t" "slice_arr" _ (by decide)]
    exact recordsLocal
  have calledCount : called.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 plan.count))) := by
    unfold called TableNew.callState
    rw [bind_lookup_other _ "t" "n" _ (by decide)]
    exact countLocal
  refine ⟨fixed_of_fields called (preparedState source plan) layout sliceFor rfl rfl fixedData,
    AllocatedLayout.mapped source plan ready domain, prefix_empty _ _ _, array_locals called layout calledRecords,
    ?_, ?_, rfl⟩
  · exact (array_lookup_other called layout "n" (by decide) (by decide) (by decide) (by decide)).trans calledCount
  · exact (array_lookup_other called layout "t" (by decide) (by decide) (by decide) (by decide)).trans (bind_lookup_same _ _ _)

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.prepare_execute
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.prepare_data
