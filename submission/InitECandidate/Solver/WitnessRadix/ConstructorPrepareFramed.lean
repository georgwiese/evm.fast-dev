import InitECandidate.Solver.WitnessRadix.ConstructorPrepare

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact BackingLayout
open Flapjack.Basis.Pure.MlString QueryBranch

theorem prepare_execute_framed {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (capacityShape : plan.capacity=4 ∨ plan.capacity%8=0)
    (capLocal : source.locals.lookup (ofString "cap")=some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 plan.table))))
    (tableCode : source.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one))
    (allocCode : source.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (zeroCode : source.code.lookup (ofString "memzero")=some (Zero.formals,Zero.body,.one))
    (enough : TableNew.price plan.capacity+1≤source.clock) :
    ∃ restoreStack : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F,
      (∀ output,emptyLocalsHOLFinite (restoreStack output)=emptyLocalsHOLFinite output) ∧
      evaluateHOLFiniteState source (.decCall (ofString "t") .one (ofString "htab_new") [.const 32#64,localVar "cap"] tableTail)=
        (let output := evaluateHOLFiniteState (preparedState source plan) (.seq recordLoop afterRecords)
         (output.1,restore source "t" (restoreStack output.2))) := by
  classical
  let called := TableNew.callState source "t" plan
  let layout := AllocatedLayout.layout plan
  have header : BuildEntry.Header called layout.table layout.keys layout.vals layout.primary layout.backup :=
    TableNew.header_of_fields {source with memory := TableNew.resultMemory source.memory source.be plan} called _ _ _ _ _ rfl rfl
      (TableNew.result_header source plan ready domain)
  have tableLocal : called.locals.lookup (ofString "t")=some (.val (.word layout.table)) := bind_lookup_same _ _ _
  obtain ⟨restoreStack,setup⟩ := array_initialize called layout tableLocal header
  have prefixRun := BuildEntry.declarations_execute setup (.seq recordLoop afterRecords)
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [.const 32#64,localVar "cap"]=some (TableNew.values plan.capacity) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,TableNew.values,capLocal]
  have callRun := TableNew.call_execute source plan "t" [.const 32#64,localVar "cap"] tableTail ready domain capacityShape args tableCode heapGlobal allocCode zeroCode enough
  refine ⟨restoreStack,BuildEntry.restoration_frame setup,?_⟩
  rw [callRun,table_tail_shape,prefixRun]
  rfl

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.prepare_execute_framed
