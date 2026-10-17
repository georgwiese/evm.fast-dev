import InitECandidate.Solver.MutableTable.WitnessBuildLoop
import InitECandidate.Solver.WitnessRadix.TableCall
import InitECandidate.Solver.PanDeclarations
import InitECandidate.Solver.WitnessRadix.TableRecords

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan) : PanSemStateFiniteExact 64 Guest.HostMemory:=
  bind (TableNew.callState source "t" plan) "i" 0#64

def finishScope (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (target : PanSemStateFiniteExact 64 Guest.HostMemory) : PanSemStateFiniteExact 64 Guest.HostMemory:=
  restore source "t" (restore (TableNew.callState source "t" plan) "i" target)

/-- The actual original table-allocation call and zero-ordinal declaration,
retaining both lexical scopes around the record-loop/return continuation. -/
theorem prepare_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (shape : plan.capacity=4 ∨ plan.capacity%8=0)
    (capLocal : source.locals.lookup (ofString "cap")=some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 plan.table))))
    (tableCode : source.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one))
    (allocCode : source.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (zeroCode : source.code.lookup (ofString "memzero")=some (Zero.formals,Zero.body,.one))
    (enough : TableNew.price plan.capacity+1≤source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString "t") .one (ofString "htab_new") [.const 32#64,localVar "cap"] tableTail)=
      (let output:=evaluateHOLFiniteState (prepared source plan) (.seq recordLoop (.return (localVar "t")));
        (output.1,finishScope source plan output.2)) := by
  let called:=TableNew.callState source "t" plan
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address))
      [.const 32#64,localVar "cap"]=some (TableNew.values plan.capacity) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,TableNew.values,capLocal]
  have callRun:=TableNew.call_execute source plan "t" _ tableTail ready domain shape args tableCode heapGlobal allocCode zeroCode enough
  have setup : BuildEntry.Initializes called [("i",.const 0#64)] (prepared source plan) (fun target=>restore called "i" target):=
    .step 0#64 rfl (.done _)
  have scopedRun:=BuildEntry.declarations_execute setup (.seq recordLoop (.return (localVar "t")))
  change evaluateHOLFiniteState called tableTail=_ at scopedRun
  rw [callRun,scopedRun]
  rfl

theorem prepare_data (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (shape : plan.capacity=4 ∨ plan.capacity%8=0) (little : source.be=false) (bits : Nat) (scratch : BitVec 64)
    (recordsLocal : source.locals.lookup (ofString "slice_arr")=some (.val (.word (BitVec.ofNat 64 plan.records))))
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 plan.count))))
    (slices : Nat→Graph.Slice) (records : Records source plan slices) :
    Layout32.Built bits (prepared source plan) plan scratch 0 [] (fun _=>none) ∧
      Locals (prepared source plan) plan 0 ∧ Records (prepared source plan) plan slices ∧
      (prepared source plan).clock=source.clock-(TableNew.price plan.capacity+1) := by
  have initial:=Layout32.initial_built source plan ready domain shape little bits scratch
  have built:=Layout32.built_fields (TableNew.enteredState source plan) (prepared source plan) plan bits scratch 0 [] (fun _=>none) rfl rfl rfl initial
  let called:=TableNew.callState source "t" plan
  have calledTable : called.locals.lookup (ofString "t")=some (.val (.word (BitVec.ofNat 64 plan.table))):=bind_lookup_same _ _ _
  have calledRecords : called.locals.lookup (ofString "slice_arr")=some (.val (.word (BitVec.ofNat 64 plan.records))):=
    (bind_lookup_other _ "t" "slice_arr" _ (by decide)).trans recordsLocal
  have calledCount : called.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 plan.count))):=
    (bind_lookup_other _ "t" "n" _ (by decide)).trans countLocal
  refine ⟨built,⟨(bind_lookup_other _ "i" "t" _ (by decide)).trans calledTable,
    (bind_lookup_other _ "i" "slice_arr" _ (by decide)).trans calledRecords,
    (bind_lookup_other _ "i" "n" _ (by decide)).trans calledCount,bind_lookup_same _ _ _⟩,?_,rfl⟩
  constructor
  · intro i inside
    change TableNew.resultMemory source.memory source.be plan (recordCell plan i 0)=.word (slices i).1
    rw [TableNew.result_earlier _ _ plan ready _ (record_earlier plan ready i 0 inside (by decide))]
    exact records.pointers i inside
  · intro i inside
    change TableNew.resultMemory source.memory source.be plan (recordCell plan i 8)=.word (slices i).2
    rw [TableNew.result_earlier _ _ plan ready _ (record_earlier plan ready i 8 inside (by decide))]
    exact records.lengths i inside

/-- Allocation updates only the heap cursor among globals and preserves the
entire concrete hash/set environment used by the original record loop. -/
theorem prepared_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64) (maximum : Nat)
    (context : Context source plan slices stp pad scratch maximum) : Context (prepared source plan) plan slices stp pad scratch maximum := by
  have globalFrame (name : MlS) (different : ofString "heap_ptr" ≠ name) :
      (prepared source plan).globals.lookup name = source.globals.lookup name := by
    simp [prepared, TableNew.callState, QueryBranch.bind, setVarHOLFinite,
      HolFiniteMapExact.update, FUPDATE, different]
  have environment : Keccak256.Environment (prepared source plan) stp pad := by
    refine ⟨context.environment.domain, ?_, ?_, context.environment.zeroCode,
      context.environment.copyCode, ?_⟩
    · exact (globalFrame (ofString "keccak_st") (by decide)).trans context.environment.stateGlobal
    · exact (globalFrame (ofString "keccak_pad") (by decide)).trans context.environment.scratchGlobal
    · exact ⟨context.environment.hashCode.block, context.environment.hashCode.perm, context.environment.hashCode.oracleEq⟩
  refine ⟨?_,context.keccakCode,environment,context.buffers,context.before,context.aligned,context.little,
    context.hashCode,context.copyCode,context.insertCode,context.memeqCode,context.findCode,context.setCode,context.lengthBound⟩
  exact (globalFrame (ofString "mpt_hash_scratch") (by decide)).trans context.global

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.prepare_execute
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.prepare_data
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.prepared_context
