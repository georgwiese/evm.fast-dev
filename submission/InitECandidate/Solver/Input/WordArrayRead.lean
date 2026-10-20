import InitECandidate.Solver.Input.WordArrayCodec
import InitECandidate.Solver.WitnessRadix.ByteArrayReads

namespace InitECandidate.Solver.Input.WordArrayRead
open Flapjack PanSemStateFiniteExact WitnessRadix

def wordBytes (word : Guest.Word) : List (BitVec 8) := (Guest.leBytes word).map byteToBits

theorem word_bytes_length (word : Guest.Word) : (wordBytes word).length = 8 := by simp [wordBytes,Guest.leBytes]

theorem bits_cons (word : Guest.Word) (rest : List Guest.Word) :
    WordArrayCodec.bits (word :: rest) = wordBytes word ++ WordArrayCodec.bits rest := by
  simp [WordArrayCodec.bits,Guest.leBytesOfWords,wordBytes]

theorem word_byte (word : Guest.Word) (offset : Nat) (inside : offset < 8) :
    (wordBytes word)[offset]'(by rw [word_bytes_length]; exact inside) = BitVec.ofNat 8 ((word.toNat / 256 ^ offset) % 256) := by
  simp [wordBytes,Guest.leBytes,byteToBits,UInt8.toBitVec_ofNat']

/-- Exact indexed bytes of the guest's actual little-endian word array. -/
theorem packed_byte (words : List Guest.Word) (offset : Nat) (inside : offset < 8 * words.length) :
    (WordArrayCodec.bits words)[offset]'(by rw [WordArrayCodec.length]; exact inside) =
      BitVec.ofNat 8 (((words[offset / 8]'(by omega)).toNat / 256 ^ (offset % 8)) % 256) := by
  induction words generalizing offset with
  | nil => simp at inside
  | cons word rest ih =>
    simp only [bits_cons]
    by_cases before : offset < 8
    · rw [List.getElem_append_left (by rw [word_bytes_length]; exact before)]
      have division : offset / 8 = 0 := Nat.div_eq_of_lt before
      have remainder : offset % 8 = offset := Nat.mod_eq_of_lt before
      simpa only [division,remainder,List.getElem_cons_zero] using word_byte word offset before
    · have past : 8 ≤ offset := by omega
      rw [List.getElem_append_right (by rw [word_bytes_length]; exact past)]
      simp only [word_bytes_length]
      have tailInside : offset - 8 < 8 * rest.length := by simp only [List.length_cons] at inside; omega
      rw [ih (offset - 8) tailInside]
      have division : offset / 8 = (offset - 8) / 8 + 1 := by omega
      have remainder : (offset - 8) % 8 = offset % 8 := by omega
      simp only [division,List.getElem_cons_succ,remainder]

/-- Pointwise actual byte loads determine the complete recursive reader,
including its exact ordered bytes and64bit address wrapping. -/
theorem read_list (pointer : BitVec 64) (bytes : List (BitVec 8)) (getByte : BitVec 64 → Option (BitVec 8))
    (read : ∀ offset, (inside : offset < bytes.length) → getByte (byteAddress pointer offset) = some (bytes[offset])) :
    readBytearrayWordHOL pointer bytes.length getByte = some bytes := by
  induction bytes generalizing pointer with
  | nil => rfl
  | cons byte rest ih =>
    have headRead : getByte pointer = some byte := by
      have current := read 0 (by simp)
      have point : byteAddress pointer 0 = pointer := by simp [byteAddress]
      rw [point] at current
      exact current
    have tailRead := ih (pointer + 1#64) (by
      intro offset inside
      have point : byteAddress (pointer + 1#64) offset = byteAddress pointer (offset + 1) := by
        simp only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc]
        rw [BitVec.add_comm (1#64 : BitVec 64) (BitVec.ofNat 64 offset)]
      have current := read (offset + 1) (by simp only [List.length_cons]; omega)
      simpa only [List.getElem_cons_succ,← point] using current)
    rw [List.length_cons,readBytearrayWordHOL,headRead]
    exact congrArg (fun output : Option (List (BitVec 8)) => output.bind (fun tail => some (byte :: tail))) tailRead

/-- The actual byte load supplied by its mapped aligned word image. -/
theorem read_byte {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (words : List Guest.Word)
    (aligned : pointer.toNat % 8 = 0) (fits : pointer.toNat + 8 * words.length < 2 ^ 64) (little : source.be = false)
    (mapped : ∀ index : Fin words.length,source.memaddrs (byteAddress pointer (8 * index.val)))
    (stored : ∀ index : Fin words.length,source.memory (byteAddress pointer (8 * index.val)) = .word (words[index.val]))
    (offset : Nat) (inside : offset < 8 * words.length) :
    @panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs (fun query => Classical.propDecidable (source.memaddrs query)) source.be
      (byteAddress pointer offset) = some ((WordArrayCodec.bits words)[offset]'(by rw [WordArrayCodec.length]; exact inside)) := by
  let index : Fin words.length := ⟨offset / 8,by omega⟩
  have cell := ByteArray.aligned_cell pointer offset (8 * words.length) inside aligned fits
  have location := byteAddress_toNat pointer offset (by omega)
  have remainder : (byteAddress pointer offset).toNat % 8 = offset % 8 := by rw [location]; omega
  have currentMapped := mapped index
  have currentStored := stored index
  have byteMapped : source.memaddrs (panByteAlignHOL (width := 64) (byteAddress pointer offset)) := by rw [cell]; exact currentMapped
  have byteStored : source.memory (panByteAlignHOL (width := 64) (byteAddress pointer offset)) = .word (words[offset / 8]) := by rw [cell]; exact currentStored
  rw [packed_byte words offset inside]
  simp only [panMemLoadByteWord8HOL,if_pos byteMapped,byteStored,little,panGetByteWord8HOL,
    Bool.false_eq_true,↓reduceIte,show 64 / 8 = 8 from rfl,remainder]

/-- A physical aligned word image supplies the actual foreign-call input
array. No future byte-read or oracle result is an entry premise. -/
theorem read_packed {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (words : List Guest.Word)
    (aligned : pointer.toNat % 8 = 0) (fits : pointer.toNat + 8 * words.length < 2 ^ 64) (little : source.be = false)
    (mapped : ∀ index : Fin words.length,source.memaddrs (byteAddress pointer (8 * index.val)))
    (stored : ∀ index : Fin words.length,source.memory (byteAddress pointer (8 * index.val)) = .word (words[index.val])) :
    readBytearrayWordHOL (byteWidth := 8) pointer (8 * words.length)
      (@panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs (fun query => Classical.propDecidable (source.memaddrs query)) source.be) =
      some (WordArrayCodec.bits words) := by
  rw [← WordArrayCodec.length words]
  apply read_list
  intro offset inside
  exact read_byte source pointer words aligned fits little mapped stored offset (by rw [WordArrayCodec.length] at inside; exact inside)

end InitECandidate.Solver.Input.WordArrayRead

#print axioms InitECandidate.Solver.Input.WordArrayRead.word_bytes_length
#print axioms InitECandidate.Solver.Input.WordArrayRead.bits_cons
#print axioms InitECandidate.Solver.Input.WordArrayRead.word_byte
#print axioms InitECandidate.Solver.Input.WordArrayRead.packed_byte
#print axioms InitECandidate.Solver.Input.WordArrayRead.read_list
#print axioms InitECandidate.Solver.Input.WordArrayRead.read_packed

#print axioms InitECandidate.Solver.Input.WordArrayRead.read_byte
