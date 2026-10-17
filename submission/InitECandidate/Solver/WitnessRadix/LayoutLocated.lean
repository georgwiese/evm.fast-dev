import InitECandidate.Solver.WitnessRadix.LayoutContext

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact

def Incoming (layout : Layout) (allocated : Nat) (word : BitVec 64) : Prop :=
  ∃ pool offset, IncomingOffset layout allocated pool offset ∧ word = cell layout pool offset

def Protected (layout : Layout) (allocated : Nat) (word : BitVec 64) : Prop :=
  leafReads layout word ∨ word = cell layout .header 24 ∨
  ∃ node < allocated, ∃ field < 3, word = cell layout .keys (32 * layout.count + 24 * node + 8 * field)

/-- Concrete addresses of installed graph components. Completed pieces are
leaves of valid ordinals; branch records stay in the already allocated prefix. -/
def Located (layout : Layout) (allocated : Nat) : OpenGraph.Tree → Prop
  | .hole slot _ => Incoming layout allocated slot
  | .complete slot root tree => Incoming layout allocated slot ∧
      ∃ ordinal < layout.count, ∃ key value, root = WordBits.leafTag ordinal ∧ tree = .leaf key value
  | .branch slot node _ zero one => Incoming layout allocated slot ∧
      (∃ index < allocated, node = branchAddress layout.keys layout.count index) ∧
      Located layout allocated zero ∧ Located layout allocated one

theorem incoming_protected (layout : Layout) (allocated : Nat) (word : BitVec 64)
    (incoming : Incoming layout allocated word) : Protected layout allocated word := by
  obtain ⟨pool, offset, inside, rfl⟩ := incoming
  cases pool with
  | header => rcases inside with rfl; exact Or.inr (Or.inl rfl)
  | keys =>
      obtain ⟨node, old, field, fields, rfl⟩ := inside
      exact Or.inr (Or.inr ⟨node, old, field, by rcases fields with rfl | rfl <;> decide, rfl⟩)
  | vals | primary | backup | records => exact False.elim inside

theorem leaf_read_global {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (valid : Valid layout) (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (immutable : Immutable source layout keyFor sliceFor) (ordinal : Nat) (inside : ordinal < layout.count)
    (key : ByteKeys.Key) (value : Graph.Slice) (query : BitVec 64)
    (read : QueryMemory.reads source layout.table layout.keys layout.vals (WordBits.leafTag ordinal) (.leaf key value) query) :
    leafReads layout query := by
  have small : ordinal < 2 ^ 63 := Nat.lt_trans inside (count_small layout valid)
  have recordWord : source.memory (layout.vals + BitVec.ofNat 64 ordinal * 8#64) = .word (record layout ordinal) := by
    rw [vals_cell]
    exact immutable.recordWord ordinal inside
  simp only [QueryMemory.reads, WordBits.leafTag_decode ordinal small, recordWord, MemoryBytes.wordBits,
    QueryMemory.leafReads] at read
  rcases read with headerKeys | headerVals | vals | pointer | length | bytes
  · exact Or.inl headerKeys
  · exact Or.inr (Or.inl headerVals)
  · exact Or.inr (Or.inr (Or.inl ⟨ordinal, inside, vals.trans (vals_cell layout ordinal)⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ordinal, inside, 0, by decide, by simpa [record] using pointer⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ordinal, inside, 1, by decide, length.trans (record_next layout ordinal)⟩)))
  · obtain ⟨byte, byteEq⟩ := bytes
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ordinal, inside, byte.val / 8, by have := byte.isLt; omega,
      byteEq.trans (hash_byte_cell layout valid ordinal inside byte)⟩)))

/-- Every actual read of a located partial graph belongs to an immutable leaf
cell or to the installed header/branch arena. -/
theorem located_reads {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) (allocated : Nat)
    (valid : Valid layout) (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (immutable : Immutable source layout keyFor sliceFor) (tree : OpenGraph.Tree) (located : Located layout allocated tree)
    (query : BitVec 64) (read : OpenGraph.reads source layout.table layout.keys layout.vals tree query) :
    Protected layout allocated query := by
  induction tree with
  | hole slot expected => exact False.elim read
  | complete slot root tree =>
      obtain ⟨incoming, ordinal, inside, key, value, rfl, rfl⟩ := located
      rcases read with slotRead | leafRead
      · subst query; exact incoming_protected layout allocated slot incoming
      · exact Or.inl (leaf_read_global source layout valid keyFor sliceFor immutable ordinal inside key value query leafRead)
  | branch slot node position zero one ihZero ihOne =>
      obtain ⟨incoming, ⟨index, bound, nodeEq⟩, zeroLocated, oneLocated⟩ := located
      rcases read with slotRead | nodeRead | zeroRead | oneRead
      · subst query; exact incoming_protected layout allocated slot incoming
      · exact Or.inr (Or.inr ⟨index, bound, 0, by decide, by simpa [cell, base, branchAddress] using nodeRead.trans nodeEq⟩)
      · exact ihZero zeroLocated zeroRead
      · exact ihOne oneLocated oneRead

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.leaf_read_global
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.located_reads
