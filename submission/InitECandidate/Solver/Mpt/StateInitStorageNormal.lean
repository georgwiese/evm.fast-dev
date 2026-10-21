import InitECandidate.Solver.Mpt.StateInitStorageProgram
import InitECandidate.Solver.Mpt.TableConstructorNormal
import InitECandidate.Solver.Mpt.StateInitPrefix
import InitECandidate.Solver.MutableTable.MemoryModelPoolFrame

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors WitnessCore MutableTable MutableTable.NaturalLayout

def storageReady (source : PanSemStateFiniteExact 64 Guest.HostMemory) (workspace heap : BitVec 64):=
  written (TableRuntime.callState source "t" .word heap.toNat 64) workspace 32 heap

/-- The first real state_init table and its actual ws+32 pointer store.
Its six-pool empty model, all decoded trie nodes and both immutable
databases survive at the actual next continuation and heap. -/
theorem storage_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db workspace : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (frozen : FrozenWitnessDatabases input (QueryBranch.bind source "db" db) workspace.toNat)
    (workspaceCell : source.globals.lookup (ofString "ws")=some (.val (.word workspace)))
    (workspaceArena : AllocatedBytes.Arena workspace 40) (workspaceAligned : workspace.toNat%8=0)
    (workspaceBefore : workspace.toNat+40≤frontier) (frontierBefore : frontier≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterRootStore=(some (.returned returned),post)) :
    let target:=storageReady source workspace heap
    let nextHeap:=BitVec.ofNat 64 (freshEnd .word heap.toNat 64)
    TableRuntime.price 64+1≤source.clock ∧
      AllocatedBytes.Arena nextHeap 0 ∧ nextHeap.toNat%8=0 ∧
      target.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧
      Valid .word (fresh .word heap.toNat 64) ∧
      MemoryModel.Header target.memory .word (fresh .word heap.toNat 64) 0#64 ∧
      MemoryModel.Occupied target .word (fresh .word heap.toNat 64) [] ∧
      FrozenWitnessDatabases input (QueryBranch.bind target "db" db) workspace.toNat ∧
      ∃ next : NodeRegistry target frontier nextHeap db,next.graph.valid=registry.graph.valid ∧
        ∃ inner,evaluateHOLFiniteState target afterStorageTrie=(some (.returned returned),inner) ∧ post=restore source "t" inner := by
  have savedFrozen:=frozen
  obtain ⟨codeArray,nodes,codes,nodeData,codeData,dbCell,nodeBefore,codeBefore⟩:=savedFrozen
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) storageArguments=some (TableRuntime.values .word 64):=rfl
  rw [storage_shapes.1] at normal
  obtain ⟨funded,valid,nextArena,nextAligned,header,occupied,prefixMemory,afterTable,sameMembers,inner,continued,endpoint⟩:=
    table_call_normal source post frontier heap db registry .word 64 (by decide) (by decide) (by decide) "t" storageArguments afterStorageTable
      heapArena heapAligned nodeData.domain nodeData.little heapCell args installed returned normal
  let entered:=TableRuntime.callState source "t" .word heap.toNat 64
  let target:=storageReady source workspace heap
  have currentWs : entered.globals.lookup (ofString "ws")=some (.val (.word workspace)):=by
    simpa [entered,TableRuntime.callState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "heap_ptr"≠ofString "ws" from by decide] using workspaceCell
  have currentT : entered.locals.lookup (ofString "t")=some (.val (.word heap)):=by
    simp [entered,TableRuntime.callState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have mapped : entered.memaddrs (workspace+32#64):=AllocatedBytes.word_mapped entered workspace 40 32 nodeData.domain workspaceArena (by decide) workspaceAligned (by decide)
  have stored:=store_execute entered workspace 32 "t" heap currentWs currentT mapped
  rw [storage_shapes.2,evaluateHOLFiniteState_seq_line780,stored] at continued
  have addressNumber : (workspace+32#64).toNat=workspace.toNat+32:=byteAddress_toNat workspace 32 (by have upper:=workspaceArena.upper; omega)
  obtain ⟨afterStore,storedMembers⟩:=afterTable.store_below entered frontier (BitVec.ofNat 64 (freshEnd .word heap.toNat 64)) db (workspace+32#64) heap (by rw [addressNumber]; omega)
  have same : afterStore.graph.valid=registry.graph.valid:=storedMembers.trans sameMembers
  have frame : MemoryModel.PoolFrame entered.memory target.memory .word (fresh .word heap.toNat 64):=by
    intro pool offset inside
    have number:=NaturalLayout.number .word (fresh .word heap.toNat 64) valid pool offset inside
    have floor:=(fresh_bounds .word heap.toNat 64 pool).1
    have away : cell (fresh .word heap.toNat 64) pool offset≠workspace+32#64:=by
      intro equal
      have numeric:=congrArg BitVec.toNat equal
      rw [number,addressNumber] at numeric
      omega
    exact if_neg away
  have targetHeader:=header.of_pool_frame entered.memory target.memory .word (fresh .word heap.toNat 64) 0#64 frame
  have targetOccupied:=occupied.of_pool_frame entered target .word (fresh .word heap.toNat 64) valid [] rfl rfl frame
  have targetFrozen:=frozen.frame input (QueryBranch.bind source "db" db) (QueryBranch.bind target "db" db) workspace.toNat rfl rfl
    ((bind_lookup_same target "db" db).trans (bind_lookup_same source "db" db).symm) (by
      intro query lower upper
      have away : query≠workspace+32#64:=by intro equal; have numeric:=congrArg BitVec.toNat equal; rw [addressNumber] at numeric; omega
      exact (if_neg away).trans (prefixMemory query (by omega)))
  have targetHeap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 (freshEnd .word heap.toNat 64)))):=by
    simp [target,storageReady,written,TableRuntime.callState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  exact ⟨funded,nextArena,nextAligned,targetHeap,valid,targetHeader,targetOccupied,targetFrozen,afterStore,same,inner,continued,endpoint⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.storage_normal
