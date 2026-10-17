import InitECandidate.Solver.WitnessRadix.ConstructorEmpty
import InitECandidate.Solver.WitnessRadix.ConstructorEnvironment
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact BackingLayout
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Real empty witness constructor call, including the record pointer0 case,
table return binding and exact caller continuation/restoration. -/
theorem empty_call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (records table : Nat)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values records 0))
    (code : source.code.lookup (ofString "nodedb_build")=some (formals,body,.one))
    (tableLower : 2701131776≤table) (tableAligned : table%8=0) (room : table+307≤33806089496)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 table))))
    (tableCode : source.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one))
    (allocCode : source.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (zeroCode : source.code.lookup (ofString "memzero")=some (Zero.formals,Zero.body,.one))
    (helperCode : source.code.lookup (ofString "solver_radix_index")=some (BuildEntry.formals,BuildProgram.body,.one))
    (enough : 48≤source.clock) :
    ∃ next root,
      let layout:=AllocatedLayout.layout (allocationPlan table table 0 4)
      next.locals=source.locals.update (ofString name,.val (.word (BitVec.ofNat 64 table))) ∧
      next.memaddrs (cell layout .header 24) ∧ next.memory (cell layout .header 24)=.word root ∧
      QueryMemory.Represents next layout.table layout.keys layout.vals root
        (initialTree (fun _ _=>0#8) (fun _=>(0#64,0#64)) (ordinals 0)) ∧
      next.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 (table+304)))) ∧
      source.clock-44≤next.clock ∧ next.clock≤source.clock ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "nodedb_build") arguments continuation)=
        let output:=evaluateHOLFiniteState next continuation
        (output.1,restore source name output.2) := by
  classical
  obtain ⟨callee,lookup,recordsLocal,countLocal⟩:=environment source.code.lookup records 0 code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,root,bodyRun,rootMapped,rootWord,represented,global,lower,upper⟩:=execute_empty entry table tableLower tableAligned room domain countLocal
    heapGlobal tableCode allocCode zeroCode helperCode (by change 47≤source.clock-1; omega)
  have actual:=Input.CallNormal.return_execute source target name .one (ofString "nodedb_build") arguments (values records 0) body continuation callee .one
    (.val (.word (BitVec.ofNat 64 table))) args lookup (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  let next:=Input.CallNormal.continuationEntry source target name (.val (.word (BitVec.ofNat 64 table)))
  refine ⟨next,root,rfl,rootMapped,rootWord,?_,global,?_,?_,actual⟩
  · exact QueryMemory.represents_of_fields target next rfl rfl rfl _ _ _ _ _ represented
  · change source.clock-44≤target.clock
    change source.clock-1-43≤target.clock at lower
    omega
  · change target.clock≤source.clock
    change target.clock≤source.clock-1 at upper
    omega

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.empty_call_execute
