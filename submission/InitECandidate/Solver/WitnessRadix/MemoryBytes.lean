import InitECandidate.Solver.WitnessRadix.MemeqByteKeys
import InitECandidate.Solver.WitnessRadix.Addressing

namespace InitECandidate.Solver.WitnessRadix.MemoryBytes
open Flapjack PanSemStateFiniteExact

structure WordView {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (words : Fin 4 → BitVec 64) : Prop where
  mapped : ∀ i : Fin 4, state.memaddrs (pointer + BitVec.ofNat 64 (8 * i.val))
  stored : ∀ i : Fin 4, state.memory (pointer + BitVec.ofNat 64 (8 * i.val)) = .word (words i)

def ByteView {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (key : ByteKeys.Key) : Prop :=
  ∀ byte : Fin 32, @panMemLoadByteHOL 64 _ state.memory state.memaddrs
    (fun address => Classical.propDecidable (state.memaddrs address)) state.be
    (pointer + BitVec.ofNat 64 byte.val) = some (Memeq32.toUInt8 (key byte))

def wordBits : HolWordLab 64 → BitVec 64
  | .word value => value

def wordsOf {F : Type} (state : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) :
    Fin 4 → BitVec 64 :=
  fun i => wordBits (state.memory (pointer + BitVec.ofNat 64 (8 * i.val)))

theorem read_of_fields {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (memory : source.memory = target.memory) (domain : source.memaddrs = target.memaddrs)
    (endian : source.be = target.be) (address : BitVec 64) :
    @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun pointer => Classical.propDecidable (source.memaddrs pointer)) source.be address =
    @panMemLoadByteHOL 64 _ target.memory target.memaddrs
      (fun pointer => Classical.propDecidable (target.memaddrs pointer)) target.be address := by
  classical
  by_cases mapped : target.memaddrs (panByteAlignHOL (width := 64) address)
  all_goals simp [panMemLoadByteHOL, memory, domain, endian, mapped]

theorem byteView_of_fields {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (memory : source.memory = target.memory) (domain : source.memaddrs = target.memaddrs)
    (endian : source.be = target.be) (pointer : BitVec 64) (key : ByteKeys.Key)
    (view : ByteView source pointer key) : ByteView target pointer key := by
  intro byte
  rw [← read_of_fields source target memory domain endian]
  exact view byte

theorem toUInt8_injective (left right : BitVec 8)
    (same : Memeq32.toUInt8 left = Memeq32.toUInt8 right) : left = right := by
  have widened := congrArg (fun byte : UInt8 => BitVec.ofNat 64 byte.toNat) same
  rw [Memeq32.widened_byte, Memeq32.widened_byte] at widened
  have narrowed := congrArg (BitVec.setWidth 8) widened
  simpa using narrowed

theorem byteView_unique {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (left right : ByteKeys.Key)
    (a : ByteView state pointer left) (b : ByteView state pointer right) : left = right := by
  funext byte
  apply toUInt8_injective
  exact Option.some.inj ((a byte).symm.trans (b byte))

theorem offset_toNat (pointer : BitVec 64) (offset : Nat)
    (fits : pointer.toNat + offset < 2 ^ 64) :
    (pointer + BitVec.ofNat 64 offset).toNat = pointer.toNat + offset :=
  byteAddress_toNat pointer offset fits

theorem aligned_offset (pointer : BitVec 64) (byte : Nat) (inside : byte < 32)
    (aligned : pointer.toNat % 8 = 0) (fits : pointer.toNat + 32 < 2 ^ 64) :
    panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 byte) =
      pointer + BitVec.ofNat 64 (8 * (byte / 8)) := by
  have address := offset_toNat pointer byte (by omega)
  have head := offset_toNat pointer (8 * (byte / 8)) (by omega)
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 64 (((pointer + BitVec.ofNat 64 byte).toNat / 8) * 8)).toNat = _
  rw [BitVec.toNat_ofNat, address, head, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Successful byte reads imply all four aligned memory cells are mapped.
The HOL word_lab carrier has exactly its Word constructor. -/
theorem byteView_words {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (key : ByteKeys.Key)
    (aligned : pointer.toNat % 8 = 0) (fits : pointer.toNat + 32 < 2 ^ 64)
    (view : ByteView state pointer key) : WordView state pointer (wordsOf state pointer) := by
  constructor
  · intro i
    let byte : Fin 32 := ⟨8 * i.val, by have := i.isLt; omega⟩
    have read := view byte
    have head := aligned_offset pointer byte.val byte.isLt aligned fits
    have division : byte.val / 8 = i.val := by dsimp [byte]; omega
    rw [division] at head
    by_contra absent
    cases memory : state.memory (pointer + BitVec.ofNat 64 (8 * i.val)) with
    | word value =>
        simp only [panMemLoadByteHOL, head, memory, absent, ↓reduceIte] at read
        cases read
  · intro i
    unfold wordsOf
    cases state.memory (pointer + BitVec.ofNat 64 (8 * i.val))
    rfl

theorem byte_from_word (pointer : BitVec 64) (byte : Fin 32) (word : BitVec 64)
    (aligned : pointer.toNat % 8 = 0) (fits : pointer.toNat + 32 < 2 ^ 64) :
    panGetByteHOL (pointer + BitVec.ofNat 64 byte.val) word false =
      Memeq32.toUInt8 ((word >>> (8 * (byte.val % 8))).setWidth 8) := by
  have address := offset_toNat pointer byte.val (by have := byte.isLt; omega)
  have digit : (pointer + BitVec.ofNat 64 byte.val).toNat % 8 = byte.val % 8 := by
    rw [address]
    omega
  have power : 256 ^ (byte.val % 8) = 2 ^ (8 * (byte.val % 8)) := by
    rw [Nat.pow_mul]
  simp only [panGetByteHOL, Bool.false_eq_true, ↓reduceIte, digit, Memeq32.toUInt8,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, power]

/-- The actual little-endian aligned-cell byte helper sees precisely the
four words' 32 bytes. All domain, range and endian premises remain explicit. -/
theorem wordView_bytes {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (words : Fin 4 → BitVec 64)
    (aligned : pointer.toNat % 8 = 0) (fits : pointer.toNat + 32 < 2 ^ 64)
    (little : state.be = false) (view : WordView state pointer words) :
    ByteView state pointer (WordKeys.key words) := by
  intro byte
  have indexSmall : byte.val / 8 < 4 := by have := byte.isLt; omega
  have indexValue : (Fin.ofNat 4 (byte.val / 8)).val = byte.val / 8 := by
    change (byte.val / 8) % 4 = byte.val / 8
    exact Nat.mod_eq_of_lt indexSmall
  have stored := view.stored (Fin.ofNat 4 (byte.val / 8))
  have mapped := view.mapped (Fin.ofNat 4 (byte.val / 8))
  rw [indexValue] at stored mapped
  have addressAligned := aligned_offset pointer byte.val byte.isLt aligned fits
  simp only [panMemLoadByteHOL, addressAligned, stored, mapped, ↓reduceIte, little]
  rw [byte_from_word pointer byte _ aligned fits]
  rfl

end InitECandidate.Solver.WitnessRadix.MemoryBytes

#print axioms InitECandidate.Solver.WitnessRadix.MemoryBytes.aligned_offset
#print axioms InitECandidate.Solver.WitnessRadix.MemoryBytes.byte_from_word
#print axioms InitECandidate.Solver.WitnessRadix.MemoryBytes.wordView_bytes
#print axioms InitECandidate.Solver.WitnessRadix.MemoryBytes.byteView_words
#print axioms InitECandidate.Solver.WitnessRadix.MemoryBytes.byteView_unique
#print axioms InitECandidate.Solver.WitnessRadix.MemoryBytes.byteView_of_fields
