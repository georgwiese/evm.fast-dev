import InitECandidate.Solver.MutableTable.WitnessDictionaryCall
import InitECandidate.Solver.MutableTable.WitnessEmptyDictionaryCall

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Uniform actual caller contract for zero and positive decoded counts.
Only a zero count may use the unused logical record arena at the table;
positive counts retain the actual decoded array address. -/
theorem paired_any_dictionary_call (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (leftArguments rightArguments : List (ExpHOL 64)) (records table count maximum : Nat)
    (leftArgs : evalListHOLFinite source (h := fun q => Classical.propDecidable (source.memaddrs q)) leftArguments = some (Constructor.values records count))
    (rightArgs : evalListHOLFinite right (h := fun q => Classical.propDecidable (right.memaddrs q)) rightArguments = some (Constructor.values records count))
    (leftCode : source.code.lookup (ofString "nodedb_build") = some (Constructor.formals, body, .one))
    (rightCode : right.code.lookup (ofString "nodedb_build") = some (Constructor.formals, Constructor.body, .one))
    (tableLower : 2701131776≤table)
    (recordsLower : 0<count → 2701131776 ≤ records) (recordsBefore : 0<count → records + 16*count ≤ table)
    (recordsAligned : 0<count → records % 8 = 0) (tableAligned : table % 8 = 0)
    (room : table + 72 + 57*(4*count+4) + 7 ≤ 33806089496)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 table))))
    (leftTableCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (rightTableCode : right.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (leftAllocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (rightAllocCode : right.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (sliceFor : BitVec 64 → Graph.Slice) (stp pad scratch : BitVec 64)
    (leftEnvironment : Keccak256.Environment source stp pad) (little : source.be=false)
    (pointers : ∀ i < count, source.memory (byteAddress (BitVec.ofNat 64 records) (16*i)) = .word (sliceFor (BitVec.ofNat 64 i)).1)
    (lengths : ∀ i < count, source.memory (byteAddress (BitVec.ofNat 64 records) (16*i+8)) = .word (sliceFor (BitVec.ofNat 64 i)).2)
    (context : 0<count → ∀ capacity, Context source (Constructor.allocationPlan records table count capacity)
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
    (leftClock : wholePrice maximum count + 2 ≤ source.clock)
    (rightClock : Constructor.wholePrice maximum count + 2 ≤ right.clock) :
    ∃ logicalRecords,∃ observation : DictionaryObservation logicalRecords table count,∃ leftTarget rightTarget,
      ConstructorPairResult source right leftTarget rightTarget leftArguments rightArguments observation sliceFor scratch maximum region safe ∧
      (count=0 → logicalRecords=table) ∧ (count≠0 → logicalRecords=records) := by
  by_cases zero : count=0
  · subst count
    have leftEnough : 48≤source.clock := by simpa [wholePrice] using leftClock
    have rightEnough : 48≤right.clock := by
      have price : Constructor.wholePrice maximum 0+2=49:=by simp [Constructor.wholePrice,Constructor.populatePrice]
      rw [price] at rightClock
      omega
    obtain ⟨observation,leftTarget,rightTarget,result⟩:=paired_empty_dictionary_call source right leftArguments rightArguments records table
      leftArgs rightArgs leftCode rightCode tableLower tableAligned (by omega) leftEnvironment.domain rightEnvironment.domain little heap
      leftTableCode rightTableCode leftAllocCode rightAllocCode leftEnvironment.zeroCode rightEnvironment.zeroCode helperCode
      scratch globals ffi region same before leftEnough rightEnough sliceFor maximum safe safeBefore
    exact ⟨table,observation,leftTarget,rightTarget,result,(by intros;rfl),(by intro impossible;exact (impossible rfl).elim)⟩
  · have positive : 0<count:=by omega
    obtain ⟨observation,leftTarget,rightTarget,result⟩:=paired_dictionary_call source right leftArguments rightArguments records table count maximum
      leftArgs rightArgs leftCode rightCode (recordsLower positive) (recordsBefore positive) (recordsAligned positive) tableAligned room heap
      leftTableCode rightTableCode leftAllocCode rightAllocCode sliceFor stp pad scratch pointers lengths (context positive)
      rightEnvironment rightHashCode helperCode locals globals endian ffi region same before recordPublic buffers
      safe safeBefore safeProtected (by omega) (by omega)
    exact ⟨records,observation,leftTarget,rightTarget,result,(by intro impossible;exact (zero impossible).elim),(by intros;rfl)⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.paired_any_dictionary_call
