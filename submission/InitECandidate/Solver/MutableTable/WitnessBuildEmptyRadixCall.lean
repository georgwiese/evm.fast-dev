import InitECandidate.Solver.MutableTable.WitnessBuildEmpty
import InitECandidate.Solver.MutableTable.WitnessBuildEnvironments
import InitECandidate.Solver.MutableTable.WitnessBuildKeyHistory
import InitECandidate.Solver.WitnessRadix.ConstructorEmptyPublic
import InitECandidate.Solver.WitnessRadix.MemoryRegionAgreement
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Actual paired empty-list callers, including the decoder's null array
pointer. No record contents, hash buffers or Keccak code are required. -/
theorem paired_empty_call (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (leftArguments rightArguments : List (ExpHOL 64)) (records table : Nat)
    (leftArgs : evalListHOLFinite source (h:=fun q=>Classical.propDecidable (source.memaddrs q)) leftArguments=some (Constructor.values records 0))
    (rightArgs : evalListHOLFinite right (h:=fun q=>Classical.propDecidable (right.memaddrs q)) rightArguments=some (Constructor.values records 0))
    (leftCode : source.code.lookup (ofString "nodedb_build")=some (Constructor.formals,body,.one))
    (rightCode : right.code.lookup (ofString "nodedb_build")=some (Constructor.formals,Constructor.body,.one))
    (tableLower : 2701131776≤table) (tableAligned : table%8=0) (room : table+307≤33806089496)
    (leftDomain : source.memaddrs=InitE.ordinaryDomain) (rightDomain : right.memaddrs=InitE.ordinaryDomain)
    (little : source.be=false)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 table))))
    (leftTableCode : source.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one))
    (rightTableCode : right.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one))
    (leftAllocCode : source.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (rightAllocCode : right.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (leftZeroCode : source.code.lookup (ofString "memzero")=some (Zero.formals,Zero.body,.one))
    (rightZeroCode : right.code.lookup (ofString "memzero")=some (Zero.formals,Zero.body,.one))
    (helperCode : right.code.lookup (ofString "solver_radix_index")=some (BuildEntry.formals,BuildProgram.body,.one))
    (scratch : BitVec 64) (globals : source.globals=right.globals) (ffi : source.ffi=right.ffi)
    (region : BitVec 64→Prop) (same : MemoryRegion.Agree region source.memory right.memory)
    (before : ∀ query,region query→query.toNat<table)
    (leftClock : 48≤source.clock) (rightClock : 48≤right.clock) :
    ∃ leftTarget rightTarget root,
      let plan:=Constructor.allocationPlan table table 0 4
      let layout:=AllocatedLayout.layout plan
      AllocatedLayout.Ready plan ∧
      evaluateHOLFiniteState source (.call (some (none,none)) (ofString "nodedb_build") leftArguments)=(none,leftTarget) ∧
      evaluateHOLFiniteState right (.call (some (none,none)) (ofString "nodedb_build") rightArguments)=(none,rightTarget) ∧
      leftTarget.locals=source.locals ∧ rightTarget.locals=right.locals ∧
      (∀ (name : String) (continuation : ProgHOL 64),
        evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "nodedb_build") leftArguments continuation)=
          (let output:=evaluateHOLFiniteState (setVarHOLFinite (ofString name) (.val (.word (BitVec.ofNat 64 table))) leftTarget) continuation;
            (output.1,restore source name output.2))) ∧
      (∀ (name : String) (continuation : ProgHOL 64),
        evaluateHOLFiniteState right (.decCall (ofString name) .one (ofString "nodedb_build") rightArguments continuation)=
          (let output:=evaluateHOLFiniteState (setVarHOLFinite (ofString name) (.val (.word (BitVec.ofNat 64 table))) rightTarget) continuation;
            (output.1,restore right name output.2))) ∧
      Layout32.Built 2 leftTarget plan scratch 0 [] (fun _=>none) ∧
      KeysMatch plan (fun _ _=>0#8) [] ∧
      rightTarget.memaddrs (BackingLayout.cell layout .header 24) ∧
      rightTarget.memory (BackingLayout.cell layout .header 24)=.word root ∧
      QueryMemory.Represents rightTarget layout.table layout.keys layout.vals root
        (BackingLayout.initialTree (fun _ _=>0#8) (fun _=>(0#64,0#64)) (BackingLayout.ordinals 0)) ∧
      leftTarget.globals=rightTarget.globals ∧ leftTarget.ffi=rightTarget.ffi ∧
      leftTarget.globals=source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (table+304)))) ∧
      MemoryRegion.Agree region leftTarget.memory rightTarget.memory ∧
      source.clock-43≤leftTarget.clock ∧ leftTarget.clock≤source.clock ∧
      right.clock-44≤rightTarget.clock ∧ rightTarget.clock≤right.clock := by
  classical
  obtain ⟨callee,leftLookup,rightLookup,_,countLocal⟩:=paired_environments source right records 0 leftCode rightCode
  let leftEntry:=callEntryStateHOLFinite source callee
  let rightEntry:=callEntryStateHOLFinite right callee
  obtain ⟨leftFinished,leftBody,built,leftFfi,leftGlobals,leftMemory,leftLower,leftUpper⟩:=execute_empty leftEntry table
    tableLower tableAligned room leftDomain little countLocal heap leftTableCode leftAllocCode leftZeroCode scratch (by change 47≤source.clock-1;omega)
  obtain ⟨rightFinished,root,rightBody,rootMapped,rootWord,represented,_,rightLower,rightUpper,rightFfi,rightGlobals,rightMemory⟩:=
    Constructor.execute_empty_public rightEntry table tableLower tableAligned room rightDomain countLocal
      (by change right.globals.lookup _=_;rw [←globals];exact heap) rightTableCode rightAllocCode rightZeroCode helperCode
      (by change 47≤right.clock-1;omega)
  let plan:=Constructor.allocationPlan table table 0 4
  let leftTarget:={leftFinished with locals:=source.locals}
  let rightTarget:={rightFinished with locals:=right.locals}
  have ready : AllocatedLayout.Ready plan:=Constructor.allocation_ready table table 0 4 tableLower (by omega)
    tableAligned tableAligned (by omega) (by omega) (by omega) (Or.inl rfl)
  have leftCall:=evaluateHOLFiniteState_call_return_caller_locals source none (ofString "nodedb_build") leftArguments
    (Constructor.values records 0) body callee .one (.val (.word (BitVec.ofNat 64 table))) leftFinished
    leftArgs leftLookup (by omega) leftBody (by simp [shapeEqHOL,shapeOfHOLExact])
  have rightCall:=evaluateHOLFiniteState_call_return_caller_locals right none (ofString "nodedb_build") rightArguments
    (Constructor.values records 0) Constructor.body callee .one (.val (.word (BitVec.ofNat 64 table))) rightFinished
    rightArgs rightLookup (by omega) rightBody (by simp [shapeEqHOL,shapeOfHOLExact])
  have finalBuilt:=Layout32.built_fields leftFinished leftTarget plan 2 scratch 0 [] (fun _=>none) rfl rfl rfl built
  refine ⟨leftTarget,rightTarget,root,ready,leftCall,rightCall,rfl,rfl,?_,?_,finalBuilt,KeysMatch.empty _ _,rootMapped,rootWord,
    QueryMemory.represents_of_fields rightFinished rightTarget rfl rfl rfl _ _ _ _ _ represented,?_,?_,leftGlobals,?_,?_,?_,?_,?_⟩
  · intro name continuation
    exact Input.CallNormal.return_execute source leftFinished name .one (ofString "nodedb_build") leftArguments
      (Constructor.values records 0) body continuation callee .one (.val (.word (BitVec.ofNat 64 table))) leftArgs leftLookup
      (by omega) leftBody (by simp [shapeEqHOL,shapeOfHOLExact])
  · intro name continuation
    exact Input.CallNormal.return_execute right rightFinished name .one (ofString "nodedb_build") rightArguments
      (Constructor.values records 0) Constructor.body continuation callee .one (.val (.word (BitVec.ofNat 64 table))) rightArgs rightLookup
      (by omega) rightBody (by simp [shapeEqHOL,shapeOfHOLExact])
  · change leftFinished.globals=rightFinished.globals
    rw [leftGlobals,rightGlobals]
    exact congrArg (fun g=>g.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (table+304))))) globals
  · exact leftFfi.trans (ffi.trans rightFfi.symm)
  · intro query inside
    exact (leftMemory query (before query inside)).trans ((same query inside).trans (rightMemory query (before query inside)).symm)
  · change source.clock-43≤leftFinished.clock
    change source.clock-1-42≤leftFinished.clock at leftLower
    omega
  · change leftFinished.clock≤source.clock
    change leftFinished.clock≤source.clock-1 at leftUpper
    omega
  · change right.clock-44≤rightFinished.clock
    change right.clock-1-43≤rightFinished.clock at rightLower
    omega
  · change rightFinished.clock≤right.clock
    change rightFinished.clock≤right.clock-1 at rightUpper
    omega

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.paired_empty_call
