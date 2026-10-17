import InitECandidate.Solver.MutableTable.WitnessBuildEmptyRadixCallControl
import InitECandidate.Solver.MutableTable.WitnessCallResult

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- The null-pointer empty-list call has the same dictionary/ABI/control API.
Its positive logical record base is unused; the actual pointer argument is
arbitrary and no record or hash-input access is introduced. -/
theorem paired_empty_dictionary_call (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
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
    (leftClock : 48≤source.clock) (rightClock : 48≤right.clock)
    (sliceFor : BitVec 64 → Graph.Slice) (maximum : Nat) (safe : BitVec 64 → Prop)
    (safeBefore : ∀ query,safe query → query.toNat<table) :
    ∃ observation : DictionaryObservation table table 0,∃ leftTarget rightTarget,
      ConstructorPairResult source right leftTarget rightTarget leftArguments rightArguments observation sliceFor scratch maximum region safe := by
  obtain ⟨leftTarget,rightTarget,root,ready,leftCall,rightCall,leftLocals,rightLocals,leftScoped,rightScoped,
    built,matching,rootMapped,rootWord,represented,finalGlobals,finalFfi,_,finalMemory,
    leftLower,leftUpper,rightLower,rightUpper,leftControl,rightControl,leftMemory,rightMemory⟩:=
    paired_empty_call_controlled source right leftArguments rightArguments records table leftArgs rightArgs leftCode rightCode
      tableLower tableAligned room leftDomain rightDomain little heap leftTableCode rightTableCode leftAllocCode rightAllocCode
      leftZeroCode rightZeroCode helperCode scratch globals ffi region same before leftClock rightClock
  let observation : DictionaryObservation table table 0:=⟨2,0,[],(fun _=>none),(fun _ _=>0#8),root⟩
  have slices : Records leftTarget observation.plan (fun index=>sliceFor (BitVec.ofNat 64 index)) := by
    constructor
    all_goals intro index inside;change index<0 at inside;omega
  have represented' : QueryMemory.Represents rightTarget (AllocatedLayout.layout observation.plan).table
      (AllocatedLayout.layout observation.plan).keys (AllocatedLayout.layout observation.plan).vals root
      (BackingLayout.initialTree observation.keyFor sliceFor (BackingLayout.ordinals 0)) := by
    change QueryMemory.Represents rightTarget _ _ _ root .empty
    exact represented
  have support : ∀ query,QueryMemory.reads rightTarget (AllocatedLayout.layout observation.plan).table
      (AllocatedLayout.layout observation.plan).keys (AllocatedLayout.layout observation.plan).vals root
      (BackingLayout.initialTree observation.keyFor sliceFor (BackingLayout.ordinals 0)) query →
      BackingLayout.Protected (AllocatedLayout.layout observation.plan) 0 query := by
    intro query read
    change False at read
    exact read.elim
  have pair : DictionaryPair leftTarget rightTarget observation sliceFor scratch:=
    ⟨by change 2≤2;decide,by change 2≤32;decide,ready,built,.empty,matching,rfl,slices,rootMapped,rootWord,represented',support⟩
  refine ⟨observation,leftTarget,rightTarget,
    ⟨⟨leftCall,leftLocals,leftScoped⟩,⟨rightCall,rightLocals,rightScoped⟩,pair,leftControl,rightControl,
      leftUpper,?_,rightUpper,?_,finalGlobals,finalFfi,finalMemory,?_,?_,(by change 4≤4;decide)⟩⟩
  · have price : wholePrice maximum 0+1=47:=by simp [wholePrice]
    rw [price];omega
  · have price : Constructor.wholePrice maximum 0+1=48:=by simp [Constructor.wholePrice,Constructor.populatePrice]
    rw [price];omega
  · intro query saved;exact leftMemory query (safeBefore query saved)
  · intro query saved;exact rightMemory query (safeBefore query saved)

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.paired_empty_dictionary_call
