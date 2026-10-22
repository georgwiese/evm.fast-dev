import InitECandidate.Solver.Mpt.StateInitBlockCompletion

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open GasBudget.Journal

theorem ready_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap workspace : BitVec 64) (key : MlS)
    (notHeap : key≠ofString "heap_ptr") (notBlock : key≠ofString "bs") :
    (ready source heap workspace).globals.lookup key=source.globals.lookup key:=by
  simp [ready,allocated,Input.putGlobal,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm notHeap,Ne.symm notBlock]

theorem completed_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) (key : MlS)
    (notHeap : key≠ofString "heap_ptr") (notScratch : key≠ofString "sk_buf") (notCap : key≠ofString "journal_cap")
    (notJournal : key≠ofString "journal") (notCounter : key≠ofString "journal_n") (notTransaction : key≠ofString "ts") :
    (completed source start).globals.lookup key=source.globals.lookup key:=by
  simp [completed,emptyLocalsHOLFinite,Initialization.initialized,Initialization.counterState,Initialization.allocatedState,Initialization.capState,scratchState,
    Input.putGlobal,HolFiniteMapExact.update,FUPDATE,Ne.symm notHeap,Ne.symm notScratch,Ne.symm notCap,Ne.symm notJournal,Ne.symm notCounter,Ne.symm notTransaction]

/-- The true state_init block suffix only updates its declared allocator
and journal globals; workspace/hash/runtime pointers are retained. -/
theorem result_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap workspace : BitVec 64) (key : MlS)
    (notHeap : key≠ofString "heap_ptr") (notBlock : key≠ofString "bs") (notScratch : key≠ofString "sk_buf") (notCap : key≠ofString "journal_cap")
    (notJournal : key≠ofString "journal") (notCounter : key≠ofString "journal_n") (notTransaction : key≠ofString "ts") :
    (resultState source heap workspace).globals.lookup key=source.globals.lookup key:=
  (completed_other (walk (ready source heap workspace) heap.toNat (PersistentAlloc.rounded heap 80#64).toNat actions)
    ((PersistentAlloc.rounded heap 80#64).toNat+70840) key notHeap notScratch notCap notJournal notCounter notTransaction).trans
    ((walk_other_global actions (ready source heap workspace) heap.toNat (PersistentAlloc.rounded heap 80#64).toNat key notHeap).trans
      (ready_other source heap workspace key notHeap notBlock))

theorem result_block_pointer (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap workspace : BitVec 64) :
    (resultState source heap workspace).globals.lookup (ofString "bs")=some (.val (.word heap)):=
  (completed_other (walk (ready source heap workspace) heap.toNat (PersistentAlloc.rounded heap 80#64).toNat actions)
    ((PersistentAlloc.rounded heap 80#64).toNat+70840) (ofString "bs") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    ((walk_other_global actions (ready source heap workspace) heap.toNat (PersistentAlloc.rounded heap 80#64).toNat (ofString "bs") (by decide)).trans
      (Input.putGlobal.lookup_same _ _ _))

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.ready_other
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.completed_other
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.result_other
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.result_block_pointer
