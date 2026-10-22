import InitECandidate.Solver.Mpt.StateInitBlockAllocation
import InitECandidate.Solver.Mpt.StateInitBlockFrame
import InitECandidate.Solver.Mpt.StateInitTailNormal
import InitECandidate.Solver.Mpt.NodeRegistryPrefixFrame
import InitECandidate.Solver.Mpt.StateInitBlockRuntime
import InitECandidate.Solver.Mpt.StateInitArithmetic

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors WitnessCore GasBudget.Journal

def resultState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap workspace : BitVec 64):=
  completed (walk (ready source heap workspace) heap.toNat (PersistentAlloc.rounded heap 80#64).toNat actions)
    ((PersistentAlloc.rounded heap 80#64).toNat+70840)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Whole original state_init suffix after its storage table: real bs80,
seven constructors, both ancestor words, sk_buf64 and journal/reset/footer.
Actual normal execution pays97source clocks and16848200fresh bytes while
retaining every older trie/database/table word and its closed registry. -/
theorem body_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db workspace oldBs oldT : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (frozen : FrozenWitnessDatabases input (QueryBranch.bind source "db" db) workspace.toNat)
    (workspaceBefore : workspace.toNat≤heap.toNat)
    (workspaceCell : source.globals.lookup (ofString "ws")=some (.val (.word workspace)))
    (bsCell : source.globals.lookup (ofString "bs")=some (.val (.word oldBs)))
    (tCell : source.locals.lookup (ofString "t")=some (.val (.word oldT)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (scalars : Input.OriginalScalarGlobals.Scalars source.globals)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterStorageTrie=(some (.returned returned),post)) :
    let finalHeap:=BitVec.ofNat 64 (heap.toNat+16848200)
    returned=.val (.word 0#64) ∧ 97≤source.clock ∧ heap.toNat+16848200≤33806089496 ∧
      post=resultState source heap workspace ∧ post.clock=source.clock-97 ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
      AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ Input.OriginalScalarGlobals.Scalars post.globals ∧
      Layouts (PersistentAlloc.rounded heap 80#64).toNat actions ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → post.memory query=source.memory query) ∧
      FrozenWitnessDatabases input (QueryBranch.bind post "db" db) workspace.toNat ∧
      ∃ next : NodeRegistry post frontier finalHeap db,next.graph.valid=registry.graph.valid := by
  have savedFrozen:=frozen
  obtain ⟨codeArray,nodes,codes,nodeData,codeData,dbCell,nodeBefore,codeBefore⟩:=savedFrozen
  obtain ⟨allocFunded,recordArena,nextArena,nextAligned,enteredHeap,enteredBs,enteredWord,enteredScalars,oldMemory,enteredFrozen,enteredRegistry,enteredMembers,fieldsRun⟩:=
    allocation_normal input source post frontier heap db workspace oldBs registry frozen workspaceBefore workspaceCell bsCell heapCell heapArena heapAligned scalars installed returned normal
  generalize enteredEq : ready source heap workspace=entered at enteredHeap enteredBs enteredWord enteredScalars oldMemory enteredFrozen enteredRegistry enteredMembers fieldsRun
  let nextHeap:=PersistentAlloc.rounded heap 80#64
  have enteredDomain : entered.memaddrs=source.memaddrs:=by rw [←enteredEq]; rfl
  have enteredEndian : entered.be=source.be:=by rw [←enteredEq]; rfl
  have enteredCode : entered.code=source.code:=by rw [←enteredEq]; rfl
  have enteredClock : entered.clock=source.clock-1:=by rw [←enteredEq]; rfl
  have enteredInstalled : Input.OriginalCode.Installed entered.code:=by rw [enteredCode]; exact installed
  have nextNumber : nextHeap.toNat=heap.toNat+80:=by
    have numeric:=PersistentAlloc.rounded_nat heap 80#64 (by have upper:=recordArena.upper; change heap.toNat+80+7<2^64; omega)
    change nextHeap.toNat=(heap.toNat+80+7)/8*8 at numeric
    omega
  have recordValid : MemoryRegion.Valid ⟨heap.toNat,80⟩:=⟨recordArena.lower,recordArena.upper,heapAligned⟩
  have currentHeap : entered.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 nextHeap.toNat))):=by
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using enteredHeap
  have currentBs : entered.globals.lookup (ofString "bs")=some (.val (.word (MemoryRegion.pointer ⟨heap.toNat,80⟩))):=by
    simpa only [MemoryRegion.pointer,BitVec.ofNat_toNat,BitVec.setWidth_eq] using enteredBs
  have currentT : entered.locals.lookup (ofString "t")=some (.val (.word oldT)):=by rw [←enteredEq]; exact tCell
  obtain ⟨layouts,fieldsFunded,fieldsBound,fieldsAligned,fieldsClock,tailRun⟩:=fields_normal entered post heap.toNat nextHeap.toNat oldT recordValid nextArena.lower
    (by have upper:=nextArena.upper; omega) nextAligned (enteredDomain.trans nodeData.domain) currentHeap currentBs currentT enteredInstalled returned fieldsRun
  generalize tablesEq : walk entered heap.toNat nextHeap.toNat actions=afterTables at fieldsClock tailRun
  have tablesHeap : afterTables.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 (nextHeap.toNat+70840)))):=by
    have actual:=walk_heap actions entered heap.toNat nextHeap.toNat currentHeap
    rw [tablesEq,cursor_all] at actual
    exact actual
  have tablesScalars : Input.OriginalScalarGlobals.Scalars afterTables.globals:=by
    rw [←tablesEq]
    exact walk_scalars actions entered heap.toNat nextHeap.toNat enteredScalars currentHeap
  have codeEq : afterTables.code=entered.code:=by
    rw [←tablesEq]
    exact walk_code actions entered heap.toNat nextHeap.toNat
  have tablesInstalled : Input.OriginalCode.Installed afterTables.code:=by rw [codeEq]; exact enteredInstalled
  obtain ⟨returnedEq,tailFunded,tailBound,postEq,postClock,postMemory,finalCell,postScalars⟩:=tail_normal afterTables post (nextHeap.toNat+70840)
    fieldsBound fieldsAligned tablesHeap tablesScalars tablesInstalled returned tailRun
  have endEq : nextHeap.toNat+70840+64+Initialization.bytes=heap.toNat+16848200:=
    block_end_arithmetic heap.toNat nextHeap.toNat nextNumber
  have endBound : heap.toNat+16848200≤33806089496:=by rwa [endEq] at tailBound
  rw [endEq] at finalCell
  have wholeFunded : 97≤source.clock:=by
    omega
  have wholeClock : post.clock=source.clock-97:=by
    omega
  have memory (query : BitVec 64) (before : query.toNat<heap.toNat) : post.memory query=source.memory query:=by
    have kept:=walk_old_word actions entered heap.toNat nextHeap.toNat recordValid actions_valid layouts query
      (by rw [nextNumber]; omega) (Or.inl before)
    rw [tablesEq] at kept
    exact (congrFun postMemory query).trans (kept.trans (oldMemory query before))
  have domain : post.memaddrs=source.memaddrs:=by
    rw [postEq]
    have actual:=walk_domain actions entered heap.toNat nextHeap.toNat
    rw [tablesEq] at actual
    exact (completed_domain afterTables (nextHeap.toNat+70840)).trans (actual.trans enteredDomain)
  have endian : post.be=source.be:=by
    rw [postEq]
    have actual:=walk_endian actions entered heap.toNat nextHeap.toNat
    rw [tablesEq] at actual
    exact (completed_endian afterTables (nextHeap.toNat+70840)).trans (actual.trans enteredEndian)
  have finalNumber : (BitVec.ofNat 64 (heap.toNat+16848200)).toNat=heap.toNat+16848200:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have finalArena : AllocatedBytes.Arena (BitVec.ofNat 64 (heap.toNat+16848200)) 0:=by
    constructor
    · rw [finalNumber]; have lower:=heapArena.lower; omega
    · rw [finalNumber]; exact endBound
  have finalAligned : (BitVec.ofNat 64 (heap.toNat+16848200)).toNat%8=0:=by rw [finalNumber]; omega
  have postFrozen:=frozen.frame input (QueryBranch.bind source "db" db) (QueryBranch.bind post "db" db) workspace.toNat domain endian
    ((bind_lookup_same post "db" db).trans (bind_lookup_same source "db" db).symm) (fun query lower upper=>memory query (upper.trans_le workspaceBefore))
  obtain ⟨next,same⟩:=registry.after_prefix source post frontier heap (BitVec.ofNat 64 (heap.toNat+16848200)) db domain (by rw [finalNumber]; omega) memory
  have resultEq : post=resultState source heap workspace:=by
    rw [resultState,enteredEq,tablesEq]
    exact postEq
  exact ⟨returnedEq,wholeFunded,endBound,resultEq,wholeClock,finalCell,finalArena,finalAligned,postScalars,layouts,memory,postFrozen,next,same⟩

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.body_normal
