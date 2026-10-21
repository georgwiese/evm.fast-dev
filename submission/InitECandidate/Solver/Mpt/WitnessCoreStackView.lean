import InitECandidate.Solver.Mpt.WitnessRecordView

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- A real activation retains its allocation frontier and the pending
hash most recently installed by the resolver. Fresh records need not have
an initialized HASH word before their first actual resolver iteration. -/
structure Entry where
  record : BitVec 64
  data : WitnessRecord.Description
  mark : Nat
  pending : Option (BitVec 64)

def top : List Entry→BitVec 64 | []=>0#64 | entry::_=>entry.record
def frames (stack : List Entry) : List WitnessStackRank.Frame:=stack.map (fun entry=>entry.data.payload.frame)

def Links (source : PanSemStateFiniteExact 64 Guest.HostMemory) : List Entry→Prop
  | []=>True
  | entry::rest=>source.memory entry.record=.word (top rest) ∧ Links source rest

def HashValid (db hash : BitVec 64) : Prop:=
  hash=0#64 ∨ 2713731432≤hash.toNat ∧ hash.toNat+32≤db.toNat

def Pending (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db : BitVec 64) (entry : Entry) : Prop:=
  match entry.pending with
  | none=>True
  | some hash=>source.memory (entry.record+80#64)=.word hash ∧ HashValid db hash

/-- Every child's real record precedes all older records, and its fresh
row/payload allocations follow all parent allocation frontiers. These
orders are preserved on pop and obtained from actual fresh decoder output
on push; they impose no ordering or acyclicity on input hashes. -/
def Ordered : List Entry→Prop
  | []=>True
  | entry::rest=>(∀ parent∈rest,entry.record.toNat+88≤parent.record.toNat ∧
      parent.mark≤entry.data.array.toNat ∧ parent.mark≤entry.data.payload.startAddress) ∧ Ordered rest

def CounterBound (data : WitnessRecord.Description) : Prop:=match data.payload with
  | .extension ..=>True
  | .branch _ index occupied=>occupied.val≤index.val

structure View (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db : BitVec 64)
    (cursor heap : Nat) (stack : List Entry) : Prop where
  records : ∀ entry∈stack,WitnessRecord.View source entry.record db entry.data
  before : ∀ entry∈stack,entry.data.BeforeHeap entry.mark
  marks : ∀ entry∈stack,entry.mark≤heap
  above : ∀ entry∈stack,cursor≤entry.record.toNat
  links : Links source stack
  pending : ∀ entry∈stack,Pending source db entry
  ordered : Ordered stack
  counters : ∀ entry∈stack,CounterBound entry.data

theorem empty (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db : BitVec 64) (cursor heap : Nat) :
    View source db cursor heap [] := by
  exact ⟨by simp,by simp,by simp,by simp,True.intro,by simp,True.intro,by simp⟩

theorem View.tail (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db : BitVec 64)
    (cursor heap : Nat) (entry : Entry) (rest : List Entry) (view : View source db cursor heap (entry::rest)) :
    View source db cursor heap rest := by
  exact ⟨fun older member=>view.records older (List.mem_cons_of_mem _ member),
    fun older member=>view.before older (List.mem_cons_of_mem _ member),
    fun older member=>view.marks older (List.mem_cons_of_mem _ member),
    fun older member=>view.above older (List.mem_cons_of_mem _ member),view.links.2,
    fun older member=>view.pending older (List.mem_cons_of_mem _ member),view.ordered.2,
    fun older member=>view.counters older (List.mem_cons_of_mem _ member)⟩

theorem View.head_nonzero (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db : BitVec 64)
    (cursor heap : Nat) (entry : Entry) (rest : List Entry) (view : View source db cursor heap (entry::rest)) : top (entry::rest)≠0#64 :=
  (view.records entry (List.mem_cons_self)).nonzero source entry.record db entry.data

theorem Links.frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stack : List Entry)
    (links : Links source stack)
    (memory : ∀ entry∈stack,target.memory entry.record=source.memory entry.record) : Links target stack := by
  induction stack with
  | nil=>trivial
  | cons entry rest ih=>
    exact ⟨(memory entry List.mem_cons_self).trans links.1,ih links.2
      (fun older member=>memory older (List.mem_cons_of_mem _ member))⟩

/-- Assemble one actual head and its already preserved physical tail. -/
theorem View.cons (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db : BitVec 64)
    (cursor heap : Nat) (entry : Entry) (rest : List Entry) (old : View source db cursor heap rest)
    (record : WitnessRecord.View source entry.record db entry.data) (before : entry.data.BeforeHeap entry.mark)
    (mark : entry.mark≤heap) (above : cursor≤entry.record.toNat) (link : source.memory entry.record=.word (top rest))
    (pending : Pending source db entry)
    (order : ∀ parent∈rest,entry.record.toNat+88≤parent.record.toNat ∧ parent.mark≤entry.data.array.toNat ∧ parent.mark≤entry.data.payload.startAddress)
    (counters : CounterBound entry.data) : View source db cursor heap (entry::rest) := by
  exact ⟨by simpa only [List.forall_mem_cons] using And.intro record old.records,
    by simpa only [List.forall_mem_cons] using And.intro before old.before,
    by simpa only [List.forall_mem_cons] using And.intro mark old.marks,
    by simpa only [List.forall_mem_cons] using And.intro above old.above,
    ⟨link,old.links⟩,
    by simpa only [List.forall_mem_cons] using And.intro pending old.pending,
    ⟨order,old.ordered⟩,
    by simpa only [List.forall_mem_cons] using And.intro counters old.counters⟩

theorem View.lower_cursor (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db : BitVec 64)
    (cursor smaller heap : Nat) (stack : List Entry) (view : View source db cursor heap stack) (drops : smaller≤cursor) :
    View source db smaller heap stack :=
  ⟨view.records,view.before,view.marks,fun entry member=>drops.trans (view.above entry member),view.links,view.pending,view.ordered,view.counters⟩

/-- Ordered older records all lie above the complete current record.
This is the actual memory cutoff for framing a head HASH/counter update. -/
theorem View.tail_after_record (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db : BitVec 64)
    (cursor heap : Nat) (entry : Entry) (rest : List Entry) (view : View source db cursor heap (entry::rest)) :
    View source db (entry.record.toNat+88) heap rest := by
  have tail:=view.tail source db cursor heap entry rest
  exact ⟨tail.records,tail.before,tail.marks,fun older member=>(view.ordered.1 older member).1,
    tail.links,tail.pending,tail.ordered,tail.counters⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.empty
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.View.tail
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.View.head_nonzero
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Links.frame

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.View.cons
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.View.lower_cursor
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.View.tail_after_record
