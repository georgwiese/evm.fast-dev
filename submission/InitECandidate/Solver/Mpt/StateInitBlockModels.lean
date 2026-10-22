import InitECandidate.Solver.Mpt.StateInitBlockEntries
import InitECandidate.Solver.Mpt.StateInitBlockFieldFrame
import InitECandidate.Solver.Mpt.StateInitBlockCompletion
import InitECandidate.Solver.GasBudget.JournalInitModel

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable MutableTable.NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch GasBudget.Journal

theorem entries_fields (specs : List Action) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (block start : Nat) (recordValid : MemoryRegion.Valid ⟨block,80⟩)
    (wellFormed : ∀ action∈specs,action.Valid) (distinct : (specs.map Action.offset).Nodup)
    (layouts : Layouts start specs) (before : block+80≤start) :
    ∀ entry∈entries start specs,(walk source block start specs).memory (MemoryRegion.address ⟨block,80⟩ entry.offset)=.word (BitVec.ofNat 64 entry.start):=by
  induction specs generalizing source start with
  | nil=>intro entry impossible; cases impossible
  | cons action rest ih=>
    have validCurrent:=wellFormed action List.mem_cons_self
    have tailValid : ∀ later∈rest,later.Valid:=fun later member=>wellFormed later (List.mem_cons_of_mem _ member)
    have noRepeat:=List.nodup_cons.mp distinct
    cases action with
    | scalar offset value=>
      intro entry member
      exact ih (stepState source block start (.scalar offset value)) start tailValid noRepeat.2 layouts.2 before entry member
    | table kind bits offset=>
      intro entry member
      rcases List.mem_cons.mp member with equal|member
      · subst entry
        apply field_after_walk rest source block start (.table kind bits offset) recordValid validCurrent tailValid layouts.2 before
        intro later member equal
        exact noRepeat.1 (List.mem_map.mpr ⟨later,member,equal.symm⟩)
      · exact ih (stepState source block start (.table kind bits offset)) (freshEnd kind start (2^bits)) tailValid noRepeat.2 layouts.2
          (before.trans (step_grows start (.table kind bits offset))) entry member

theorem action_offsets_distinct : (actions.map Action.offset).Nodup:=by decide

def objects (start : Nat) (index : Fin (entries start actions).length) : TableFamily.Object:=
  ((entries start actions)[index]).object

theorem table_count (start : Nat) : (entries start actions).length=7:=rfl

/-- The actual table family, stored block pointers and reserved empty
journal after the original block suffix. All geometry comes from the real
constructor layouts and final allocator bound. -/
def Initialized (post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap workspace : BitVec 64) : Prop:=
  let start:=(PersistentAlloc.rounded heap 80#64).toNat
  let journalBase:=start+70840+64
  let finalCursor:=heap.toNat+16848200
  post.globals.lookup (ofString "bs")=some (.val (.word heap)) ∧
    post.memory heap=.word workspace ∧
    post.memory (MemoryRegion.address ⟨heap.toNat,80⟩ 56)=.word 0#64 ∧
    post.memory (MemoryRegion.address ⟨heap.toNat,80⟩ 64)=.word 0#64 ∧
    TableFamily.Model post finalCursor (objects start) ∧
    (∀ index,(post.memory (MemoryRegion.address ⟨heap.toNat,80⟩ ((entries start actions)[index]).offset))=
      .word ((objects start index).pointer)) ∧
    Zone (objects start) journalBase Initialization.capacity finalCursor ∧
    (∀ entries : Nat→Entry (Fin (entries start actions).length),Image post (objects start) journalBase 0 entries) ∧
    post.globals.lookup (ofString "journal_cap")=some (.val (.word (BitVec.ofNat 64 Initialization.capacity))) ∧
    post.globals.lookup (ofString "journal")=some (.val (.word (BitVec.ofNat 64 journalBase))) ∧
    post.globals.lookup (ofString "journal_n")=some (.val (.word 0#64)) ∧
    post.globals.lookup (ofString "ts")=some (.val (.word 0#64))

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.entries_fields
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.action_offsets_distinct
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.table_count
