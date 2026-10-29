import InitECandidate.Solver.GasBudget.Frame
import InitECandidate.Solver.Mpt.TrieWalkProgram
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget
open WitnessRadix WitnessRadix.QueryBranch

/-- Physical facts about the original node's compact path. Lengths are raw
words; the walk may reject an overlong path before touching its bytes. -/
structure PathView (memory : Memory) (domain : BitVec 64 → Prop) (node : BitVec 64) where
  size : BitVec 64
  pointer : BitVec 64
  sizeMapped : domain (node + 40#64)
  sizeStored : memory (node + 40#64) = .word size
  pointerMapped : domain (node + 32#64)
  pointerStored : memory (node + 32#64) = .word pointer
  fits : pointer.toNat + min size.toNat 64 < 2^64
  mapped : ∀ offset < min size.toNat 64, domain (panByteAlignHOL (width := 64) (byteAddress pointer offset))

structure ChildView (memory : Memory) (domain : BitVec 64 → Prop) (valid : BitVec 64 → Prop) (address : BitVec 64) where
  child : BitVec 64
  mapped : domain address
  stored : memory address = .word child
  member : valid child

/-- A current physical graph, with closed child pointers. This is an entry
condition for a local walk theorem; deriving it from original constructors,
decoding and every mutation is a separate reachability obligation. -/
structure Graph (memory : Memory) (domain : BitVec 64 → Prop) where
  valid : BitVec 64 → Prop
  null : valid 0#64
  header : ∀ node, valid node → node ≠ 0#64 → domain node ∧ memory node = .word (wordAt memory node)
  path : ∀ node, valid node → node ≠ 0#64 →
    (wordAt memory node = 1#64 ∨ wordAt memory node = 2#64) → PathView memory domain node
  extension : ∀ node, valid node → node ≠ 0#64 → wordAt memory node = 2#64 →
    ChildView memory domain valid (node + 48#64)
  zeroHop : ∀ node (member : valid node) (active : node ≠ 0#64) (tag : wordAt memory node = 2#64),
    wordAt memory (node + 40#64) = 0#64 →
      let child := (extension node member active tag).child
      child = 0#64 ∨ wordAt memory child ≠ 2#64
  branch : ∀ node, valid node → node ≠ 0#64 →
    wordAt memory node ≠ 0#64 → wordAt memory node ≠ 1#64 → wordAt memory node ≠ 2#64 →
    ∀ index, index < 16 → ChildView memory domain valid (node + 32#64 + BitVec.ofNat 64 (index * 8))
  /-- Every registered node was initialized with an original tag0,1,2or3. -/
  kindBound : ∀ node, valid node → node≠0#64 → (wordAt memory node).toNat≤3

/-- The actual key byte buffer, including the nibble range needed to keep
branch child selection within the original sixteen-slot array. -/
structure KeyView (memory : Memory) (domain : BitVec 64 → Prop) (be : Bool) (pointer : BitVec 64) (length : Nat) where
  small : length ≤ 64
  fits : pointer.toNat + length < 2^64
  mapped : ∀ offset < length, domain (panByteAlignHOL (width := 64) (byteAddress pointer offset))
  nibble : ∀ offset < length, ∃ value : UInt8, value.toNat < 16 ∧
    @panMemLoadByteHOL 64 _ memory domain (fun address => Classical.propDecidable (domain address))
      be (byteAddress pointer offset) = some value

theorem PathView.size_word (memory : Memory) (domain : BitVec 64 → Prop) (node : BitVec 64)
    (view : PathView memory domain node) : wordAt memory (node + 40#64) = view.size := by
  simp [wordAt, view.sizeStored, MemoryBytes.wordBits]

theorem KeyView.window_fits (memory : Memory) (domain : BitVec 64 → Prop) (be : Bool)
    (pointer position : BitVec 64) (length count : Nat) (view : KeyView memory domain be pointer length)
    (bounded : position.toNat ≤ length) (within : count ≤ length - position.toNat) :
    (pointer + position).toNat + count < 2^64 := by
  have addition : (pointer + position).toNat = pointer.toNat + position.toNat :=
    BitVec.toNat_add_of_lt (by have fits := view.fits; omega)
  have fits := view.fits
  rw [addition]
  omega

theorem KeyView.window_mapped (memory : Memory) (domain : BitVec 64 → Prop) (be : Bool)
    (pointer position : BitVec 64) (length count : Nat) (view : KeyView memory domain be pointer length)
    (bounded : position.toNat ≤ length) (within : count ≤ length - position.toNat) :
    ∀ offset < count, domain (panByteAlignHOL (width := 64) (byteAddress (pointer + position) offset)) := by
  intro offset inside
  have mapped := view.mapped (position.toNat + offset) (by omega)
  simpa [byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using mapped

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.PathView.size_word
#print axioms InitECandidate.Solver.Mpt.TrieWalk.KeyView.window_fits
#print axioms InitECandidate.Solver.Mpt.TrieWalk.KeyView.window_mapped
