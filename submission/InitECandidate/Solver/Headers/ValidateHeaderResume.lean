import InitECandidate.Solver.Headers.ValidateRound

namespace InitECandidate.Solver.Headers.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- The actual original header return resumes the same loop row with its
new allocated header and derived current heap. Full input/row/hash/scratch
context is retained before the real pointer store and hash call. -/
theorem RoundState.after_header (data : Data) (origin source target : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (heap header : BitVec 64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (returned : Decode.Returned source target (data.pointers index) (data.lengths index) heap data.cursor data.limit data.lower header) :
    RoundState data origin (Input.CallNormal.continuationEntry source target "h" (.val (.word header))) index := by
  let ready:=Input.CallNormal.continuationEntry source target "h" (.val (.word header))
  obtain ⟨actualHeap,actualCell,bound,heapAligned,hashesBefore⟩ := state.heap
  have same : actualHeap=heap := by
    have h:=Option.some.inj (actualCell.symm.trans heapCell)
    cases h
    rfl
  subst actualHeap
  have before : data.upper≤heap.toNat := by have a:=layout.inputBefore; have b:=layout.hsBeforeHashes; omega
  have frame : Input.HashInput.Frame source ready data.lower data.upper :=
    ⟨fun query lower upper=>returned.memory.words query lower (upper.trans_le before)⟩
  have nextArena:=Rlp.Validation.Arena.of_fields target ready data.cursor data.limit returned.arena rfl rfl
  have environment : Keccak256.Environment ready data.stp data.pad :=
    Keccak256.Environment.of_fields source ready data.stp data.pad state.environment returned.domain returned.code returned.oracle returned.globals
  have lookup (key : MlS) (different : key≠ofString "h") : ready.locals.lookup key=source.locals.lookup key := by
    simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm different]
  have guards:=PersistentAlloc.guards header 248#64 returned.allocation.upper
  refine ⟨?_,?_,nextArena,environment,state.input.trans origin source ready data.lower data.upper frame,
    state.rows.of_frame source ready data.array data.pointers data.lengths data.count data.lower data.upper frame,?_,
    (lookup _ (by decide)).trans state.arrayCell,(lookup _ (by decide)).trans state.countCell,
    (lookup _ (by decide)).trans state.hsCell,(lookup _ (by decide)).trans state.hashesCell,(lookup _ (by decide)).trans state.indexCell,?_⟩
  · change Input.OriginalCode.Installed target.code
    rw [returned.code]
    exact state.installed
  · change target.eshapes.lookup _=_
    rw [returned.exceptions]
    exact state.shape
  · refine ⟨PersistentAlloc.rounded header 248#64,returned.heapGlobal,guards.2.2.2.1,guards.2.2.2.2,?_⟩
    have first:=returned.afterHeap
    have next:=guards.2.2.1
    omega
  · intro key other
    exact (returned.globals key other).trans (state.globals key other)

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.RoundState.after_header
