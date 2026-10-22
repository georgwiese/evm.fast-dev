import InitECandidate.Solver.Mpt.StateInitBlockTable

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable

def Action.offset : Action → Nat
  | .table _ _ offset=>offset
  | .scalar offset _=>offset

def Action.value (start : Nat) : Action → BitVec 64
  | .table ..=>BitVec.ofNat 64 start
  | .scalar _ value=>value

theorem step_field (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat) (action : Action) :
    (stepState source block start action).memory (MemoryRegion.address ⟨block,80⟩ action.offset)=.word (action.value start):=by
  cases action <;> exact if_pos rfl

/-- A field store preserves every other older word, including fields of
the same block record. Constructor writes start at the current heap. -/
theorem step_word_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat) (action : Action)
    (layout : StepLayout start action) (query : BitVec 64) (before : query.toNat<start)
    (away : query≠MemoryRegion.address ⟨block,80⟩ action.offset) :
    (stepState source block start action).memory query=source.memory query:=by
  cases action with
  | scalar offset value=>exact if_neg away
  | table kind bits offset=>
    exact (if_neg away).trans (TableRuntime.caller_memory_away source "t" kind start (2^bits) layout query (Or.inl before))

theorem walk_word_away (specs : List Action) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (block start : Nat)
    (layouts : Layouts start specs) (query : BitVec 64) (before : query.toNat<start)
    (away : ∀ action∈specs,query≠MemoryRegion.address ⟨block,80⟩ action.offset) :
    (walk source block start specs).memory query=source.memory query:=by
  induction specs generalizing source start with
  | nil=>rfl
  | cons action rest ih=>
    exact (ih (stepState source block start action) (stepCursor start action) layouts.2
      (before.trans_le (step_grows start action)) (fun later member=>away later (List.mem_cons_of_mem _ member))).trans
      (step_word_away source block start action layouts.1 query before (away action List.mem_cons_self))

/-- Real completed field values survive all later constructors/stores at
different block offsets; this covers each table pointer and ancestor zero. -/
theorem field_after_walk (specs : List Action) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (block start : Nat) (action : Action) (recordValid : MemoryRegion.Valid ⟨block,80⟩)
    (validAction : action.Valid) (wellFormed : ∀ later∈specs,later.Valid)
    (layouts : Layouts (stepCursor start action) specs) (before : block+80≤start)
    (different : ∀ later∈specs,action.offset≠later.offset) :
    (walk (stepState source block start action) block (stepCursor start action) specs).memory
      (MemoryRegion.address ⟨block,80⟩ action.offset)=.word (action.value start):=by
  have offsetBound : action.offset+8≤80:=by
    cases action with
    | table kind bits offset=>exact validAction.2.2.1
    | scalar offset value=>exact validAction.1
  have addressNumber:=MemoryRegion.address_number ⟨block,80⟩ recordValid action.offset (by change action.offset≤80; omega)
  apply Eq.trans (walk_word_away specs _ block (stepCursor start action) layouts _ ?_ ?_) (step_field source block start action)
  · rw [addressNumber]
    have grows:=step_grows start action
    change block+action.offset<stepCursor start action
    omega
  · intro later member equal
    have laterBound : later.offset+8≤80:=by
      have validLater:=wellFormed later member
      cases later with
      | table kind bits offset=>exact validLater.2.2.1
      | scalar offset value=>exact validLater.1
    have numeric:=congrArg BitVec.toNat equal
    rw [addressNumber,MemoryRegion.address_number ⟨block,80⟩ recordValid later.offset (by change later.offset≤80; omega)] at numeric
    apply different later member
    change block+action.offset=block+later.offset at numeric
    omega

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.step_field
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.step_word_away
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.walk_word_away
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.field_after_walk
