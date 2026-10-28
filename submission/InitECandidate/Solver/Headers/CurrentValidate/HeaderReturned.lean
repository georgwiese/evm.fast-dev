import InitECandidate.Solver.Headers.CurrentValidate.Round

namespace InitECandidate.Solver.Headers.CurrentValidate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix

/-- The same current loop row survives a genuine original header return.
Its actual fresh header/next heap protect prior input before hashing. -/
theorem RoundState.after_header (data : Data) (origin source target : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (heap header : BitVec 64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (returned : CurrentDecode.Returned source target heap header (data.lengths index).toNat) :
    RoundState data origin (CallNormal.continuationEntry source target "h" (.val (.word header))) index := by
  let ready:=CallNormal.continuationEntry source target "h" (.val (.word header))
  obtain ⟨actualHeap,actualCell,bound,heapAligned,hashesBefore⟩:=state.heap
  have same : actualHeap=heap := by
    have h:=Option.some.inj (actualCell.symm.trans heapCell)
    cases h
    rfl
  subst actualHeap
  have before : data.upper≤heap.toNat := by have a:=layout.inputBefore; have b:=layout.hsBeforeHashes; omega
  have frame : HashInput.Frame source ready data.lower data.upper := ⟨fun query lower upper=>returned.memory query (Nat.lt_of_lt_of_le upper before)⟩
  have nextArena : CurrentStartup.ArenaState ready := returned.arena.of_frame rfl
  have environment : CurrentKeccak.Hash.Environment ready data.stp data.pad :=
    ⟨nextArena.code,nextArena.domain,
      (returned.globals (ofString "keccak_st") (by decide)).trans state.environment.stateGlobal,
      (returned.globals (ofString "keccak_pad") (by decide)).trans state.environment.padGlobal,
      state.environment.stateArena,state.environment.padArena,state.environment.stateAligned,state.environment.padAligned⟩
  have lookup (key : MlS) (different : key≠ofString "h") : ready.locals.lookup key=source.locals.lookup key := by
    simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm different]
  have guards:=PersistentAlloc.guards header 248#64 returned.room
  refine ⟨nextArena,environment,state.input.trans origin source ready data.lower data.upper frame,
    state.rows.of_frame source ready data.array data.pointers data.lengths data.count data.lower data.upper frame,?_,
    (lookup _ (by decide)).trans state.arrayCell,(lookup _ (by decide)).trans state.countCell,
    (lookup _ (by decide)).trans state.hsCell,(lookup _ (by decide)).trans state.hashesCell,(lookup _ (by decide)).trans state.indexCell,?_⟩
  · refine ⟨PersistentAlloc.rounded header 248#64,returned.heapGlobal,guards.2.2.2.1,guards.2.2.2.2,?_⟩
    have first:=returned.afterHeap
    have next:=guards.2.2.1
    omega
  · intro key different
    exact (returned.globals key different).trans (state.globals key different)

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.RoundState.after_header
