import InitECandidate.Solver.WitnessRadix.QueryLeafIteration
import InitECandidate.Solver.WitnessRadix.Graph

namespace InitECandidate.Solver.WitnessRadix.QueryMemory
open Flapjack PanSemStateFiniteExact
open QueryLeaf

/-- A read-only representation stated directly in the actual HOL memory.
Construction must establish it; lookup never assumes a successful execution. -/
def Represents {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table keys vals : BitVec 64) : BitVec 64 → Graph.Tree → Prop
  | root, .empty => root = 0#64
  | root, .leaf key value =>
      ∃ ordinal : Nat, ∃ record : BitVec 64,
        ordinal < 2 ^ 63 ∧ root = WordBits.leafTag ordinal ∧
        LeafCells source table keys vals (BitVec.ofNat 64 ordinal) record value.1 value.2 ∧
        MemoryBytes.ByteView source (keys + BitVec.ofNat 64 ordinal * 32#64) key ∧
        (keys + BitVec.ofNat 64 ordinal * 32#64).toNat + 32 < 2 ^ 64
  | root, .branch position zero one =>
      root ≠ 0#64 ∧ root &&& 1#64 = 0#64 ∧ position < 256 ∧
      source.memaddrs root ∧ source.memory root = .word (BitVec.ofNat 64 position) ∧
      source.memaddrs (root + 8#64) ∧ source.memaddrs (root + 16#64) ∧
      ∃ zeroRoot oneRoot : BitVec 64,
        source.memory (root + 8#64) = .word zeroRoot ∧
        source.memory (root + 16#64) = .word oneRoot ∧
        Represents source table keys vals zeroRoot zero ∧
        Represents source table keys vals oneRoot one

theorem cells_of_fields {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (memory : source.memory = target.memory) (domain : source.memaddrs = target.memaddrs)
    (table keys vals ordinal record pointer length : BitVec 64)
    (cells : LeafCells source table keys vals ordinal record pointer length) :
    LeafCells target table keys vals ordinal record pointer length := by
  rcases cells with ⟨a,b,c,d,e,f,g,h,i,j⟩
  rw [memory] at b d f i j
  rw [domain] at a c e g h
  exact ⟨a,b,c,d,e,f,g,h,i,j⟩

theorem represents_of_fields {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (memory : source.memory = target.memory) (domain : source.memaddrs = target.memaddrs)
    (endian : source.be = target.be) (table keys vals root : BitVec 64)
    (tree : Graph.Tree) (rep : Represents source table keys vals root tree) :
    Represents target table keys vals root tree := by
  induction tree generalizing root with
  | empty => exact rep
  | leaf key value =>
      obtain ⟨ordinal, record, small, tag, cells, view, fits⟩ := rep
      exact ⟨ordinal, record, small, tag,
        cells_of_fields source target memory domain _ _ _ _ _ _ _ cells,
        MemoryBytes.byteView_of_fields source target memory domain endian _ _ view, fits⟩
  | branch position zero one ihZero ihOne =>
      obtain ⟨nonzero, even, inside, mapped, bitWord, zeroMapped, oneMapped,
        zeroRoot, oneRoot, zeroWord, oneWord, zeroRep, oneRep⟩ := rep
      rw [memory] at bitWord zeroWord oneWord
      rw [domain] at mapped zeroMapped oneMapped
      exact ⟨nonzero, even, inside, mapped, bitWord, zeroMapped, oneMapped,
        zeroRoot, oneRoot, zeroWord, oneWord, ihZero _ zeroRep, ihOne _ oneRep⟩

theorem narrow_byte (byte : BitVec 8) :
    BitVec.ofNat 8 (Memeq32.toUInt8 byte).toNat = byte := by
  have equality := congrArg (BitVec.setWidth 8) (Memeq32.widened_byte byte)
  simpa using equality

/-- A byte view supplies exactly the byte used by the candidate's branch,
including its natural shift amount and byte-to-word conversion. -/
theorem query_digit {F : Type} (source : PanSemStateFiniteExact 64 F)
    (hash : BitVec 64) (key : ByteKeys.Key) (position : Nat) (inside : position < 256)
    (view : MemoryBytes.ByteView source hash key) :
    ∃ byte : UInt8,
      @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be
        (hash + (BitVec.ofNat 64 position >>> (3 : Nat))) = some byte ∧
      (WordBits.digit (BitVec.ofNat 8 byte.toNat) (BitVec.ofNat 64 position) = 0#64 ↔
        ByteKeys.bit key position = false) := by
  classical
  let index : Fin 32 := ⟨position / 8, by omega⟩
  refine ⟨Memeq32.toUInt8 (key index), ?_, ?_⟩
  · have address : BitVec.ofNat 64 position >>> (3 : Nat) = BitVec.ofNat 64 (position / 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [WordBits.shift3, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show position < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
    rw [address]
    exact view index
  · rw [narrow_byte, WordBits.digit_zero]
    have encoded : (BitVec.ofNat 64 position).toNat = position := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [encoded]
    have indexEq : Fin.ofNat 32 (position / 8) = index := by
      apply Fin.ext
      exact ByteKeys.byte_index position inside
    simp only [ByteKeys.bit, indexEq]

end InitECandidate.Solver.WitnessRadix.QueryMemory

#print axioms InitECandidate.Solver.WitnessRadix.QueryMemory.represents_of_fields
#print axioms InitECandidate.Solver.WitnessRadix.QueryMemory.query_digit
