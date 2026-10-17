import InitECandidate.Solver.MutableTable.WitnessCallResult

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- The complete actual paired constructor contract in the dictionary relation
used by sequential map initialization. All entry obligations remain explicit. -/
theorem paired_dictionary_call (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (leftArguments rightArguments : List (ExpHOL 64)) (records table count maximum : Nat)
    (leftArgs : evalListHOLFinite source (h := fun q => Classical.propDecidable (source.memaddrs q)) leftArguments = some (Constructor.values records count))
    (rightArgs : evalListHOLFinite right (h := fun q => Classical.propDecidable (right.memaddrs q)) rightArguments = some (Constructor.values records count))
    (leftCode : source.code.lookup (ofString "nodedb_build") = some (Constructor.formals, body, .one))
    (rightCode : right.code.lookup (ofString "nodedb_build") = some (Constructor.formals, Constructor.body, .one))
    (recordsLower : 2701131776 ≤ records) (recordsBefore : records + 16*count ≤ table)
    (recordsAligned : records % 8 = 0) (tableAligned : table % 8 = 0)
    (room : table + 72 + 57*(4*count+4) + 7 ≤ 33806089496)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 table))))
    (leftTableCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (rightTableCode : right.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (leftAllocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (rightAllocCode : right.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (sliceFor : BitVec 64 → Graph.Slice) (stp pad scratch : BitVec 64)
    (pointers : ∀ i < count, source.memory (byteAddress (BitVec.ofNat 64 records) (16*i)) = .word (sliceFor (BitVec.ofNat 64 i)).1)
    (lengths : ∀ i < count, source.memory (byteAddress (BitVec.ofNat 64 records) (16*i+8)) = .word (sliceFor (BitVec.ofNat 64 i)).2)
    (context : ∀ capacity, Context source (Constructor.allocationPlan records table count capacity)
      (fun i => sliceFor (BitVec.ofNat 64 i)) stp pad scratch maximum)
    (rightEnvironment : Keccak256.Environment right stp pad)
    (rightHashCode : right.code.lookup (ofString "keccak256") = some (Keccak256.formals, Keccak256.body, .one))
    (helperCode : right.code.lookup (ofString "solver_radix_index") = some (BuildEntry.formals, BuildProgram.body, .one))
    (locals : source.locals = right.locals) (globals : source.globals = right.globals)
    (endian : source.be = right.be) (ffi : source.ffi = right.ffi)
    (region : BitVec 64 → Prop) (same : MemoryRegion.Agree region source.memory right.memory)
    (before : ∀ query, region query → query.toNat < table)
    (recordPublic : ∀ i < count, region (byteAddress (BitVec.ofNat 64 records) (16*i)) ∧
      region (byteAddress (BitVec.ofNat 64 records) (16*i+8)))
    (buffers : ∀ i < count, Keccak256.BufferRegion region stp (sliceFor (BitVec.ofNat 64 i)).1 pad scratch
      (sliceFor (BitVec.ofNat 64 i)).2.toNat)
    (safe : BitVec 64 → Prop)
    (safeBefore : ∀ query,safe query → query.toNat<table)
    (safeProtected : ∀ query,safe query → Keccak256.Protected stp pad scratch query)
    (leftClock : wholePrice maximum count + 1 ≤ source.clock)
    (rightClock : Constructor.wholePrice maximum count + 1 ≤ right.clock) :
    ∃ observation : DictionaryObservation records table count,∃ leftTarget rightTarget,
      ConstructorPairResult source right leftTarget rightTarget leftArguments rightArguments observation sliceFor scratch maximum region safe := by
  obtain ⟨bits,finalCount,input,logical,keyFor,leftTarget,rightTarget,root,bitsLow,bitsTop,ready,
    leftCall,rightCall,leftLocals,rightLocals,_,leftScoped,rightScoped,nextBuilt,nextHistory,nextMatching,nextLength,nextRecords,
    rootMapped,rootWord,represented,leftControl,rightControl,leftUpper,leftLower,rightUpper,rightLower,
    finalGlobals,finalFfi,finalMemory,leftFrame,rightFrame,support,capacityBound⟩:=
    paired_call_execute_supported source right leftArguments rightArguments records table count maximum
      leftArgs rightArgs leftCode rightCode recordsLower recordsBefore recordsAligned tableAligned room heap
      leftTableCode rightTableCode leftAllocCode rightAllocCode sliceFor stp pad scratch pointers lengths context
      rightEnvironment rightHashCode helperCode locals globals endian ffi region same before recordPublic buffers
      safe safeBefore safeProtected leftClock rightClock
  let observation : DictionaryObservation records table count:=⟨bits,finalCount,input,logical,keyFor,root⟩
  exact ⟨observation,leftTarget,rightTarget,
    ⟨⟨leftCall,leftLocals,leftScoped⟩,⟨rightCall,rightLocals,rightScoped⟩,
      ⟨bitsLow,bitsTop,ready,nextBuilt,nextHistory,nextMatching,nextLength,nextRecords,rootMapped,rootWord,represented,support⟩,
      leftControl,rightControl,leftUpper,leftLower,rightUpper,rightLower,finalGlobals,finalFfi,finalMemory,leftFrame,rightFrame,capacityBound⟩⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.paired_dictionary_call
