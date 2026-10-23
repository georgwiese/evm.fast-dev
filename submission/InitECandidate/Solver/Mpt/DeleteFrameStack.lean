import InitECandidate.Solver.Mpt.DeleteFrameMemory

namespace InitECandidate.Solver.Mpt.DeleteFrame
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Proof data for one physical saved activation, using precisely the
scalar words read by the actual push. No functional trie is introduced. -/
structure Saved where
  pointer : BitVec 64
  kind : Kind
  words : String→BitVec 64

def Saved.previous (saved : Saved) : BitVec 64:=saved.words "top"
def Saved.node (saved : Saved) : BitVec 64:=saved.words "node"

structure Saved.View (source : PanSemStateFiniteExact 64 Guest.HostMemory) (saved : Saved) : Prop where
  arena : AllocatedBytes.Arena saved.pointer 40
  aligned : saved.pointer.toNat%8=0
  before : saved.pointer.toNat+40≤ceiling
  cells : ∀ field∈saved.kind.fields saved.words,
    source.memory (saved.pointer+BitVec.ofNat 64 field.offset)=.word field.value.word

theorem Saved.View.nonzero (source : PanSemStateFiniteExact 64 Guest.HostMemory) (saved : Saved)
    (view : saved.View source) : saved.pointer≠0#64 := by
  intro zero
  have floor:=view.arena.lower
  rw [zero] at floor
  contradiction

theorem Saved.View.previous_cell (source : PanSemStateFiniteExact 64 Guest.HostMemory) (saved : Saved)
    (view : saved.View source) : source.memory saved.pointer=.word saved.previous := by
  have member : (⟨0,.saved "top" (saved.words "top")⟩ : LocalFields.Field)∈saved.kind.fields saved.words:=by
    cases saved.kind <;> simp [Kind.fields]
  simpa only [Saved.previous,LocalFields.Operand.word,BitVec.add_zero] using view.cells _ member

theorem Saved.View.of_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (saved : Saved)
    (view : saved.View source)
    (memory : ∀ query : BitVec 64,saved.pointer.toNat≤query.toNat→query.toNat<saved.pointer.toNat+40→target.memory query=source.memory query) :
    saved.View target := by
  refine ⟨view.arena,view.aligned,view.before,?_⟩
  intro field member
  have inside:=(saved.kind.geometry saved.words field member).1
  have number:=byteAddress_toNat saved.pointer field.offset (by have upper:=view.arena.upper; omega)
  change (saved.pointer+BitVec.ofNat 64 field.offset).toNat=saved.pointer.toNat+field.offset at number
  rw [memory _ (by rw [number]; omega) (by rw [number]; omega)]
  exact view.cells field member

theorem Saved.View.of_written (source : PanSemStateFiniteExact 64 Guest.HostMemory) (saved : Saved)
    (arena : AllocatedBytes.Arena saved.pointer 40) (aligned : saved.pointer.toNat%8=0)
    (before : saved.pointer.toNat+40≤ceiling) :
    saved.View {source with memory:=written saved.kind source.memory saved.pointer saved.words} :=
  ⟨arena,aligned,before,written_cells saved.kind source.memory saved.pointer saved.words⟩

/-- Actual PREV links and initialized cells of the whole active scratch
stack. The list records its finite physical history, independently of any
sharing or cycles in the trie nodes saved inside those records. -/
def Stack (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (top : BitVec 64) : List Saved→Prop
  | []=>top=0#64
  | saved::tail=>top=saved.pointer ∧ cursor≤saved.pointer.toNat ∧ saved.View source ∧ Stack source cursor saved.previous tail

theorem Stack.of_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (top : BitVec 64)
    (frames : List Saved) (stack : Stack source cursor top frames)
    (memory : ∀ query : BitVec 64,cursor≤query.toNat→query.toNat<ceiling→target.memory query=source.memory query) :
    Stack target cursor top frames := by
  induction frames generalizing top with
  | nil=>exact stack
  | cons saved tail ih=>
    obtain ⟨same,above,view,rest⟩:=stack
    refine ⟨same,above,view.of_memory source target saved ?_,ih saved.previous rest⟩
    intro query lower upper
    exact memory query (above.trans lower) (upper.trans_le view.before)

theorem Stack.lower_cursor (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor smaller : Nat) (top : BitVec 64)
    (frames : List Saved) (stack : Stack source cursor top frames) (decreases : smaller≤cursor) :
    Stack source smaller top frames := by
  induction frames generalizing top with
  | nil=>exact stack
  | cons saved tail ih=>
    obtain ⟨same,above,view,rest⟩:=stack
    exact ⟨same,decreases.trans above,view,ih saved.previous rest⟩

/-- Every actual push adds one fresh lower record and retains all
previous PREV cells. Allocation geometry supplies the memory separation. -/
theorem Stack.push (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (top : BitVec 64)
    (frames : List Saved) (stack : Stack source cursor top frames) (saved : Saved)
    (view : saved.View target) (previous : saved.previous=top) (before : saved.pointer.toNat+40≤cursor)
    (memory : ∀ query : BitVec 64,cursor≤query.toNat→query.toNat<ceiling→target.memory query=source.memory query) :
    Stack target saved.pointer.toNat saved.pointer (saved::frames) := by
  refine ⟨rfl,Nat.le_refl _,view,?_⟩
  rw [previous]
  exact (stack.of_memory source target cursor top frames memory).lower_cursor target cursor saved.pointer.toNat top frames (by omega)

/-- A nonempty top reads its genuine saved PREV, and the next stack has
exactly one fewer frame. No monotonicity of trie child pointers is used. -/
theorem Stack.pop (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (top : BitVec 64)
    (frames : List Saved) (stack : Stack source cursor top frames) (active : top≠0#64) :
    ∃ saved tail,frames=saved::tail ∧ top=saved.pointer ∧ saved.View source ∧
      source.memory top=.word saved.previous ∧ Stack source cursor saved.previous tail ∧ tail.length+1=frames.length := by
  cases frames with
  | nil=>exact False.elim (active stack)
  | cons saved tail=>
    obtain ⟨same,_,view,rest⟩:=stack
    exact ⟨saved,tail,rfl,same,view,(by rw [same]; exact view.previous_cell source saved),rest,rfl⟩

end InitECandidate.Solver.Mpt.DeleteFrame

#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Saved.View.nonzero
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Saved.View.previous_cell
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Saved.View.of_memory
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Saved.View.of_written
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Stack.of_memory
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Stack.lower_cursor
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Stack.push
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Stack.pop
