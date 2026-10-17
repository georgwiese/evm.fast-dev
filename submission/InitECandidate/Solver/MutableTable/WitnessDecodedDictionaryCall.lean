import InitECandidate.Solver.MutableTable.WitnessAnyDictionaryCall
import InitECandidate.Solver.MutableTable.WitnessEntryEnvironment
import InitECandidate.Solver.MutableTable.WitnessDecodedData

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Real normal decoder records supply the entire constructor memory contract,
including the null empty-list case. Fixed startup arenas/code, allocation
ordering, prior public agreement and enough clocks remain explicit. -/
theorem paired_decoded_dictionary_call (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (pointer array : BitVec 64) (start length boundary table maximum : Nat)
    (decoded : Input.VarList.Records source input pointer array start length)
    (leftArguments rightArguments : List (ExpHOL 64))
    (leftArgs : evalListHOLFinite source (h:=fun q=>Classical.propDecidable (source.memaddrs q)) leftArguments=
      some (Constructor.values (Input.VarList.decodedArray array length).toNat (Input.VarList.decodedCount input start length)))
    (rightArgs : evalListHOLFinite right (h:=fun q=>Classical.propDecidable (right.memaddrs q)) rightArguments=
      some (Constructor.values (Input.VarList.decodedArray array length).toNat (Input.VarList.decodedCount input start length)))
    (leftCode : source.code.lookup (ofString "nodedb_build")=some (Constructor.formals,body,.one))
    (rightCode : right.code.lookup (ofString "nodedb_build")=some (Constructor.formals,Constructor.body,.one))
    (tableLower : 2701131776≤table) (tableAligned : table%8=0)
    (room : table+72+57*(4*Input.VarList.decodedCount input start length+4)+7≤33806089496)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 table))))
    (leftTableCode : source.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one))
    (rightTableCode : right.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one))
    (leftAllocCode : source.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (rightAllocCode : right.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (stp pad scratch : BitVec 64) (entry : EntryEnvironment source stp pad scratch)
    (rightEnvironment : Keccak256.Environment right stp pad)
    (rightHashCode : right.code.lookup (ofString "keccak256")=some (Keccak256.formals,Keccak256.body,.one))
    (helperCode : right.code.lookup (ofString "solver_radix_index")=some (BuildEntry.formals,BuildProgram.body,.one))
    (stateArena : Arena stp 200) (stateAligned : stp.toNat%8=0)
    (paddingArena : Arena pad 136) (paddingAligned : pad.toNat%8=0) (outputArena : Arena scratch 32)
    (buffersBefore : stp.toNat+200≤array.toNat ∧ pad.toNat+136≤array.toNat ∧ scratch.toNat+32≤array.toNat)
    (arrayBefore : array.toNat+16*Input.VarList.decodedCount input start length≤boundary)
    (boundaryBefore : boundary≤table)
    (lengthBound : ∀ index<Input.VarList.decodedCount input start length,
      (Input.VarList.recordLength input start length (Input.VarList.decodedCount input start length) index).toNat≤maximum)
    (locals : source.locals=right.locals) (globals : source.globals=right.globals) (endian : source.be=right.be) (ffi : source.ffi=right.ffi)
    (same : MemoryRegion.Agree (fun query=>query.toNat<boundary) source.memory right.memory)
    (safe : BitVec 64 → Prop) (safeBefore : ∀ query,safe query → query.toNat<table)
    (safeProtected : ∀ query,safe query → Keccak256.Protected stp pad scratch query)
    (leftClock : wholePrice maximum (Input.VarList.decodedCount input start length)+2≤source.clock)
    (rightClock : Constructor.wholePrice maximum (Input.VarList.decodedCount input start length)+2≤right.clock) :
    ∃ logicalRecords,∃ observation : DictionaryObservation logicalRecords table (Input.VarList.decodedCount input start length),∃ leftTarget rightTarget,
      ConstructorPairResult source right leftTarget rightTarget leftArguments rightArguments observation
        (decodedSlice input pointer start length) scratch maximum (fun query=>query.toNat<boundary) safe ∧
      (Input.VarList.decodedCount input start length=0 → logicalRecords=table) ∧
      (Input.VarList.decodedCount input start length≠0 → logicalRecords=(Input.VarList.decodedArray array length).toNat) := by
  classical
  let count:=Input.VarList.decodedCount input start length
  let rawRecords:=(Input.VarList.decodedArray array length).toNat
  have nonempty (positive : 0<count) : length≠0 := by
    intro zero
    simp only [count,Input.VarList.decodedCount,if_pos zero] at positive
    omega
  have rawEq (positive : 0<count) : rawRecords=array.toNat := by
    simp only [rawRecords,Input.VarList.decodedArray,if_neg (nonempty positive)]
  have facts (positive : 0<count) := decoded_constructor_data source input pointer array start length boundary
    entry.environment.domain decoded (nonempty positive) arrayBefore stp pad scratch stateArena stateAligned paddingArena paddingAligned outputArena buffersBefore
  have countSmall : count<2^31 := (Input.VarList.Records.cells source input pointer array start length entry.environment.domain decoded).2.1
  have sizes (index : Nat) (inside : index<count) : (decodedSlice input pointer start length (BitVec.ofNat 64 index)).2.toNat≤maximum := by
    have fits : index<2^64:=by omega
    simp only [decodedSlice,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fits]
    exact lengthBound index inside
  apply paired_any_dictionary_call source right leftArguments rightArguments rawRecords table count maximum leftArgs rightArgs leftCode rightCode
    tableLower _ _ _ tableAligned room heap leftTableCode rightTableCode leftAllocCode rightAllocCode
    (decodedSlice input pointer start length) stp pad scratch entry.environment entry.little _ _ _
    rightEnvironment rightHashCode helperCode locals globals endian ffi (fun query=>query.toNat<boundary) same
    (by intro query inside;omega) _ _ safe safeBefore safeProtected leftClock rightClock
  · intro positive
    rw [rawEq positive]
    exact (facts positive).2.1
  · intro positive
    rw [rawEq positive]
    omega
  · intro positive
    rw [rawEq positive]
    exact (facts positive).2.2.1
  · intro index inside
    rw [rawEq (by omega)]
    exact (facts (by omega)).2.2.2.1 index inside
  · intro index inside
    rw [rawEq (by omega)]
    exact (facts (by omega)).2.2.2.2.1 index inside
  · intro positive capacity
    apply EntryEnvironment.context source (Constructor.allocationPlan rawRecords table count capacity)
      (fun index=>decodedSlice input pointer start length (BitVec.ofNat 64 index)) stp pad scratch maximum entry
    · exact (facts positive).2.2.2.2.2.1
    · change stp.toNat+200≤rawRecords ∧ pad.toNat+136≤rawRecords ∧ scratch.toNat+32≤rawRecords
      rw [rawEq positive]
      exact buffersBefore
    · exact sizes
  · intro index inside
    rw [rawEq (by omega)]
    exact (facts (by omega)).2.2.2.2.2.2.2 index inside
  · intro index inside
    exact (facts (by omega)).2.2.2.2.2.2.1 index inside

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.paired_decoded_dictionary_call
