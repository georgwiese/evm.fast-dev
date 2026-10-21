import InitECandidate.Solver.Mpt.StateInitBlockProgram
import InitECandidate.Solver.Mpt.StateInitRootInstalled
import InitECandidate.Solver.WitnessRadix.AllocationGlobalNormal

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors WitnessCore WitnessCore.Stack

def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  Input.putGlobal (PersistentAlloc.post {source with clock:=source.clock-1} heap 80#64) "bs" heap
def ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap workspace : BitVec 64):=
  {allocated source heap with memory:=StoreWord.put source.memory heap workspace}

/-- The actual block-state allocation and workspace link derive their
room/funding from the normal run. All old trie nodes and older persistent
words remain intact before the seven real table initializations. -/
theorem allocation_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db workspace oldBs : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (frozen : FrozenWitnessDatabases input (QueryBranch.bind source "db" db) workspace.toNat)
    (workspaceBefore : workspace.toNat≤heap.toNat)
    (workspaceCell : source.globals.lookup (ofString "ws")=some (.val (.word workspace)))
    (bsCell : source.globals.lookup (ofString "bs")=some (.val (.word oldBs)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (scalars : Input.OriginalScalarGlobals.Scalars source.globals)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterStorageTrie=(some (.returned returned),post)) :
    let target:=ready source heap workspace
    let nextHeap:=PersistentAlloc.rounded heap 80#64
    1≤source.clock ∧ AllocatedBytes.Arena heap 80 ∧ AllocatedBytes.Arena nextHeap 0 ∧ nextHeap.toNat%8=0 ∧
      target.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧
      target.globals.lookup (ofString "bs")=some (.val (.word heap)) ∧ target.memory heap=.word workspace ∧
      Input.OriginalScalarGlobals.Scalars target.globals ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      FrozenWitnessDatabases input (QueryBranch.bind target "db" db) workspace.toNat ∧
      ∃ next : NodeRegistry target frontier nextHeap db,next.graph.valid=registry.graph.valid ∧
        evaluateHOLFiniteState target afterWorkspace=(some (.returned returned),post) := by
  have oldFrozen:=frozen
  obtain ⟨codeArray,nodes,codes,nodeData,codeData,dbCell,nodeBefore,codeBefore⟩:=oldFrozen
  have safe : Input.LocalPrefix (ofString "t") allocate:=.globalCall _ _ _
  rw [shapes.1] at normal
  obtain ⟨middle,allocRun,continued,localFrame⟩:=safe.normal_continue source post afterAllocation returned normal
  obtain ⟨room,funded,middleEq⟩:=PersistentAlloc.global_call_normal source middle "bs" oldBs heap 80#64 bsCell [.const 80#64] rfl
    (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapCell (by have upper:=heapArena.upper; omega) allocRun
  change middle=allocated source heap at middleEq
  subst middle
  let entered:=allocated source heap
  let target:=ready source heap workspace
  let nextHeap:=PersistentAlloc.rounded heap 80#64
  have arena : AllocatedBytes.Arena heap 80:=⟨heapArena.lower,room⟩
  have guards:=PersistentAlloc.guards heap 80#64 room
  have nextBound : nextHeap.toNat≤33806089496:=guards.2.2.2.1
  have nextAligned : nextHeap.toNat%8=0:=guards.2.2.2.2
  have grows : heap.toNat≤nextHeap.toNat:=by have paid:=guards.2.2.1; change heap.toNat+80≤nextHeap.toNat at paid; omega
  have nextArena : AllocatedBytes.Arena nextHeap 0:=⟨heapArena.lower.trans grows,by omega⟩
  have enteredBs : entered.globals.lookup (ofString "bs")=some (.val (.word heap)):=Input.putGlobal.lookup_same _ _ _
  have enteredWs : entered.globals.lookup (ofString "ws")=some (.val (.word workspace)):=by
    simpa [entered,allocated,Input.putGlobal,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
      show ofString "bs"≠ofString "ws" from by decide,show ofString "heap_ptr"≠ofString "ws" from by decide] using workspaceCell
  have mapped : entered.memaddrs heap:=by
    simpa [byteAddress] using AllocatedBytes.word_mapped entered heap 80 0 nodeData.domain arena (by decide) heapAligned (by decide)
  have addressRead : eval entered (addConst (.var .global (ofString "bs")) 0#64)=some (.val (.word heap)):=by
    simp [eval,addConst,evalHOLExact,evalListHOLExact,toExact,enteredBs,valueIsWord,valueWord,wordOpHOL,wordOp]
  have valueRead : eval entered (.var .global (ofString "ws"))=some (.val (.word workspace)):=by simp [eval,evalHOLExact,toExact,enteredWs]
  have storeRun : evaluateHOLFiniteState entered storeWorkspace=(none,target):=StoreWord.execute entered _ _ heap workspace addressRead valueRead mapped
  rw [shapes.2.1,evaluateHOLFiniteState_seq_line780,storeRun] at continued
  obtain ⟨allocatedRegistry,allocatedMembers⟩:=registry.of_fields source entered frontier heap db rfl rfl
  obtain ⟨storedRegistry,storedMembers⟩:=allocatedRegistry.store_above entered frontier heap db heap workspace (Nat.le_refl _)
  let next:=storedRegistry.advance_heap target frontier heap nextHeap db grows
  have same : next.graph.valid=registry.graph.valid:=storedMembers.trans allocatedMembers
  have memory (query : BitVec 64) (before : query.toNat<heap.toNat) : target.memory query=source.memory query:=by
    have away : query≠heap:=by intro equal; subst query; omega
    exact if_neg away
  have targetFrozen:=frozen.frame input (QueryBranch.bind source "db" db) (QueryBranch.bind target "db" db) workspace.toNat rfl rfl
    ((bind_lookup_same target "db" db).trans (bind_lookup_same source "db" db).symm)
    (fun query lower upper=>memory query (upper.trans_le workspaceBefore))
  have targetHeap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)):=by
    simp [target,ready,allocated,Input.putGlobal,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
      show ofString "bs"≠ofString "heap_ptr" from by decide,nextHeap]
  have targetScalars : Input.OriginalScalarGlobals.Scalars target.globals:=
    (scalars.update (ofString "heap_ptr") nextHeap).update (ofString "bs") heap
  exact ⟨funded,arena,nextArena,nextAligned,targetHeap,enteredBs,by simp [target,ready,StoreWord.put],targetScalars,memory,targetFrozen,next,same,continued⟩

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.allocation_normal
