import InitECandidate.Solver.Mpt.StateInitBlockFieldsNormal

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- One real initialized field changes only its owned block record; the
constructor writes are above the actual incoming persistent cursor. -/
theorem step_old_word (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat) (action : Action)
    (recordValid : MemoryRegion.Valid ⟨block,80⟩) (validAction : action.Valid) (layout : StepLayout start action)
    (query : BitVec 64) (before : query.toNat<start) (outside : query.toNat<block ∨ block+80≤query.toNat) :
    (stepState source block start action).memory query=source.memory query := by
  have away (offset : Nat) (inside : offset+8≤80) : query≠MemoryRegion.address ⟨block,80⟩ offset:=by
    intro equal
    have numeric:=congrArg BitVec.toNat equal
    rw [MemoryRegion.address_number ⟨block,80⟩ recordValid offset (by change offset≤80; omega)] at numeric
    change query.toNat=block+offset at numeric
    omega
  cases action with
  | scalar offset value=>exact if_neg (away offset validAction.1)
  | table kind bits offset=>
    exact (if_neg (away offset validAction.2.2.1)).trans
      (TableRuntime.caller_memory_away source "t" kind start (2^bits) layout query (Or.inl before))

/-- All older words outside the block record survive the complete actual
table/field prefix. This includes old trie nodes, databases, earlier table
pools and any already initialized table that a later step must retain. -/
theorem walk_old_word (specs : List Action) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat)
    (recordValid : MemoryRegion.Valid ⟨block,80⟩) (wellFormed : ∀ action∈specs,action.Valid) (layouts : Layouts start specs)
    (query : BitVec 64) (before : query.toNat<start) (outside : query.toNat<block ∨ block+80≤query.toNat) :
    (walk source block start specs).memory query=source.memory query := by
  induction specs generalizing source start with
  | nil=>rfl
  | cons action rest ih=>
    have grows : start≤stepCursor start action:=by cases action <;> dsimp only [stepCursor,NaturalLayout.freshEnd] <;> omega
    exact (ih (stepState source block start action) (stepCursor start action) (fun later member=>wellFormed later (List.mem_cons_of_mem _ member))
      layouts.2 (before.trans_le grows)).trans (step_old_word source block start action recordValid (wellFormed action List.mem_cons_self) layouts.1 query before outside)

theorem step_other_global (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat) (action : Action) (key : Flapjack.Pancake.PanLang.MlS)
    (other : key≠ofString "heap_ptr") : (stepState source block start action).globals.lookup key=source.globals.lookup key:=by
  cases action <;> simp [stepState,writeField,TableRuntime.callState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm other]

theorem walk_other_global (specs : List Action) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat) (key : Flapjack.Pancake.PanLang.MlS)
    (other : key≠ofString "heap_ptr") : (walk source block start specs).globals.lookup key=source.globals.lookup key:=by
  induction specs generalizing source start with
  | nil=>rfl
  | cons action rest ih=>exact (ih (stepState source block start action) (stepCursor start action)).trans (step_other_global source block start action key other)

theorem walk_heap (specs : List Action) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 start)))) :
    (walk source block start specs).globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 (cursor start specs)))):=by
  induction specs generalizing source start with
  | nil=>exact heap
  | cons action rest ih=>
    rw [cursor_cons]
    exact ih (stepState source block start action) (stepCursor start action) (step_heap source block start action heap)

theorem walk_scalars (specs : List Action) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat)
    (scalars : Input.OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 start)))) :
    Input.OriginalScalarGlobals.Scalars (walk source block start specs).globals:=by
  intro key member
  by_cases isHeap : key=ofString "heap_ptr"
  · subst key; exact ⟨BitVec.ofNat 64 (cursor start specs),walk_heap specs source block start heap⟩
  · obtain ⟨word,cell⟩:=scalars key member
    exact ⟨word,(walk_other_global specs source block start key isHeap).trans cell⟩

def runtimeFields (source : PanSemStateFiniteExact 64 Guest.HostMemory):=
  (source.code,source.memaddrs,source.be,source.eshapes,source.ffi)

theorem walk_runtime (specs : List Action) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat) :
    runtimeFields (walk source block start specs)=runtimeFields source:=by
  induction specs generalizing source start with
  | nil=>rfl
  | cons action rest ih=>
    rw [walk,ih]
    cases action <;> rfl

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.step_old_word
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.walk_old_word
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.step_other_global
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.walk_other_global
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.walk_heap
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.walk_scalars
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.walk_runtime
