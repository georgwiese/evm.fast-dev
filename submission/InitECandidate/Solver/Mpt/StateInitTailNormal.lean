import InitECandidate.Solver.Mpt.StateInitBlockProgram
import InitECandidate.Solver.GasBudget.JournalInitFields
import InitECandidate.Solver.Input.OriginalScalarGlobals

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open GasBudget.Journal

def allocateScratch : ProgHOL 64:=.call (some (some (.global,ofString "sk_buf"),none)) (ofString "alloc") [.const 64#64]
def scratchState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat):=
  Input.putGlobal {source with globals:=source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (start+64)))),clock:=source.clock-1} "sk_buf" (BitVec.ofNat 64 start)
def completed (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat):=
  emptyLocalsHOLFinite (Initialization.initialized (scratchState source start) (start+64))

set_option maxRecDepth 100000 in
theorem tail_shape : afterFields=.seq allocateScratch Initialization.selected:=by
  rw [Initialization.actual_site]
  simp only [afterFields,drop,actions,afterWorkspace,afterAllocation,afterStorageTrie,afterStorageTable,afterRootStore,afterRoot,rootCall,
    afterSecond,afterFirst,StateInit.afterAllocation,body,Guest.guestFn_state_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    allocateScratch,Initialization.program,Initialization.setCap,Initialization.allocate,Initialization.allocationArguments,Initialization.afterAllocation,
    Initialization.resetCounter,Initialization.resetTransaction,Initialization.capacity]

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem tail_names : ofString "sk_buf"∈Input.OriginalScalarGlobals.names ∧ ofString "journal"∈Input.OriginalScalarGlobals.names:=by decide_cbv

/-- The actual final state_init suffix derives both remaining allocations
and all journal resets. It spends exactly2source clocks, preserves all
ordinary memory and returns the exact original initialized global state. -/
theorem tail_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat)
    (bounded : start≤33806089496) (aligned : start%8=0)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 start))))
    (scalars : Input.OriginalScalarGlobals.Scalars source.globals) (installed : Input.OriginalCode.Installed source.code)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterFields=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ 2≤source.clock ∧ start+64+Initialization.bytes≤33806089496 ∧
      post=completed source start ∧ post.clock=source.clock-2 ∧ post.memory=source.memory ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 (start+64+Initialization.bytes)))) ∧
      Input.OriginalScalarGlobals.Scalars post.globals := by
  obtain ⟨oldSk,skCell⟩:=scalars _ tail_names.1
  obtain ⟨oldJournal,journalCell⟩:=scalars _ tail_names.2
  have safe : Input.LocalPrefix (ofString "setup") allocateScratch:=.globalCall _ _ _
  rw [tail_shape] at normal
  obtain ⟨middle,allocRun,journalRun,saved⟩:=safe.normal_continue source post Initialization.selected returned normal
  have nextAligned : (start+64)%8=0:=by omega
  obtain ⟨scratchRoom,scratchBound,funded,middleEq⟩:=PersistentAlloc.global_call_normal_expected source middle "sk_buf" oldSk start 64 (start+64)
    bounded (by decide) (Nat.le_refl _) (by omega) nextAligned skCell [.const 64#64] rfl (PersistentAlloc.original_code source.code installed)
    (Input.Trap.original_code source.code installed) heap allocRun
  change middle=scratchState source start at middleEq
  subst middle
  have scratchHeap : (scratchState source start).globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 (start+64)))):=by
    simp [scratchState,Input.putGlobal,HolFiniteMapExact.update,FUPDATE,show ofString "sk_buf"≠ofString "heap_ptr" from by decide]
  have scratchJournal : (scratchState source start).globals.lookup (ofString "journal")=some (.val (.word oldJournal)):=by
    simpa [scratchState,Input.putGlobal,HolFiniteMapExact.update,FUPDATE,show ofString "sk_buf"≠ofString "journal" from by decide,
      show ofString "heap_ptr"≠ofString "journal" from by decide] using journalCell
  obtain ⟨returnedEq,finalBound,journalFunded,postEq⟩:=Initialization.normal (scratchState source start) post (start+64) oldJournal scratchBound nextAligned scratchJournal scratchHeap
    (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) returned journalRun
  have wholeFunded : 2≤source.clock:=by change 1≤source.clock-1 at journalFunded; omega
  have postClock : post.clock=source.clock-2:=by rw [postEq]; change source.clock-1-1=source.clock-2; omega
  have finalHeap:=Initialization.globals (scratchState source start) (start+64)
  have scratchScalars : Input.OriginalScalarGlobals.Scalars (scratchState source start).globals:=
    (scalars.update (ofString "heap_ptr") (BitVec.ofNat 64 (start+64))).update (ofString "sk_buf") (BitVec.ofNat 64 start)
  have postScalars : Input.OriginalScalarGlobals.Scalars post.globals:=by
    rw [postEq]
    exact ((((scratchScalars.update (ofString "journal_cap") (BitVec.ofNat 64 Initialization.capacity)).update (ofString "heap_ptr") (BitVec.ofNat 64 (start+64+Initialization.bytes))).update
      (ofString "journal") (BitVec.ofNat 64 (start+64))).update (ofString "journal_n") 0#64).update (ofString "ts") 0#64
  exact ⟨returnedEq,wholeFunded,finalBound,postEq,postClock,by rw [postEq]; rfl,by rw [postEq]; exact finalHeap.1,postScalars⟩

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.tail_shape
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.tail_names
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.tail_normal
