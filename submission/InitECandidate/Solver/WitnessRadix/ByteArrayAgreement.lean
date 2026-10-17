import InitECandidate.Solver.WitnessRadix.ByteArrayFrame

namespace InitECandidate.Solver.WitnessRadix.ByteArray
open Flapjack PanSemStateFiniteExact

/-- Array reads depend only on the individual bytes requested, including
failure and address wrapping. -/
theorem read_congr (pointer : BitVec 64) (length : Nat)
    (left right : BitVec 64 → Option (BitVec 8))
    (same : ∀ offset < length,
      left (byteAddress pointer offset) = right (byteAddress pointer offset)) :
    readBytearrayWordHOL pointer length left = readBytearrayWordHOL pointer length right := by
  induction length generalizing pointer with
  | zero => rfl
  | succ length ih =>
    have head := same 0 (by omega)
    have tail := ih (pointer + 1) (by
      intro offset inside
      have next := same (1 + offset) (by omega)
      simpa only [byteAddress, BitVec.ofNat_add, BitVec.add_assoc,
        show (1 : BitVec 64) = 1#64 from by decide] using next)
    have headEq : left pointer = right pointer := by simpa [byteAddress] using head
    rw [readBytearrayWordHOL, readBytearrayWordHOL, headEq, tail]

theorem read_word8_of_cell {F G : Type}
    (source : PanSemStateFiniteExact 64 F) (target : PanSemStateFiniteExact 64 G)
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (address : BitVec 64)
    (word : source.memory (panByteAlignHOL (width := 64) address) =
      target.memory (panByteAlignHOL (width := 64) address)) :
    @panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs
      (fun query => Classical.propDecidable (source.memaddrs query)) source.be address =
    @panMemLoadByteWord8HOL 64 _ target.memory target.memaddrs
      (fun query => Classical.propDecidable (target.memaddrs query)) target.be address := by
  classical
  simp only [panMemLoadByteWord8HOL, domain, endian, word]

/-- No equality of code, globals, locals, clocks or unrelated memory is
required to obtain the same foreign-call input array. -/
theorem read_of_cells {F G : Type}
    (source : PanSemStateFiniteExact 64 F) (target : PanSemStateFiniteExact 64 G)
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (pointer : BitVec 64) (length : Nat)
    (words : ∀ offset < length,
      source.memory (panByteAlignHOL (width := 64) (byteAddress pointer offset)) =
      target.memory (panByteAlignHOL (width := 64) (byteAddress pointer offset))) :
    readBytearrayWordHOL (byteWidth := 8) pointer length
      (@panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs
        (fun query => Classical.propDecidable (source.memaddrs query)) source.be) =
    readBytearrayWordHOL (byteWidth := 8) pointer length
      (@panMemLoadByteWord8HOL 64 _ target.memory target.memaddrs
        (fun query => Classical.propDecidable (target.memaddrs query)) target.be) := by
  apply read_congr
  intro offset inside
  exact read_word8_of_cell source target domain endian _ (words offset inside)

/-- Writing the same bytes preserves agreement on any chosen set of words.
The exact tail-first writer's failed-store fallback is included. -/
theorem write_agrees (left right : BitVec 64 → HolWordLab 64)
    (domain : BitVec 64 → Prop) (endian : Bool) (region : BitVec 64 → Prop)
    (same : ∀ query, region query → left query = right query)
    (pointer : BitVec 64) (bytes : List (BitVec 8)) :
    ∀ query, region query →
      (@panWriteBytearrayWord8HOL 64 _ pointer bytes left domain
        (fun query => Classical.propDecidable (domain query)) endian) query =
      (@panWriteBytearrayWord8HOL 64 _ pointer bytes right domain
        (fun query => Classical.propDecidable (domain query)) endian) query := by
  classical
  induction bytes generalizing pointer with
  | nil => exact same
  | cons byte rest ih =>
    intro query inside
    let aligned := panByteAlignHOL (width := 64) pointer
    have tail := ih (pointer + 1)
    cases leftCell : (@panWriteBytearrayWord8HOL 64 _ (pointer + 1) rest left domain
        (fun query => Classical.propDecidable (domain query)) endian) aligned with
    | word leftValue =>
      cases rightCell : (@panWriteBytearrayWord8HOL 64 _ (pointer + 1) rest right domain
          (fun query => Classical.propDecidable (domain query)) endian) aligned with
      | word rightValue =>
        by_cases mapped : domain aligned
        · by_cases hit : query = aligned
          · have cellEq := tail query inside
            rw [hit, leftCell, rightCell] at cellEq
            have valueEq : leftValue = rightValue := by injection cellEq
            simp only [panWriteBytearrayWord8HOL, panMemStoreByteWord8HOL,
              show panByteAlignHOL (width := 64) pointer = aligned from rfl,
              leftCell, rightCell, if_pos mapped, if_pos hit, valueEq]
          · simpa only [panWriteBytearrayWord8HOL, panMemStoreByteWord8HOL,
              show panByteAlignHOL (width := 64) pointer = aligned from rfl,
              leftCell, rightCell, if_pos mapped, if_neg hit] using tail query inside
        · simpa only [panWriteBytearrayWord8HOL, panMemStoreByteWord8HOL,
            show panByteAlignHOL (width := 64) pointer = aligned from rfl,
            leftCell, rightCell, if_neg mapped] using same query inside

theorem write_of_cells {F G : Type}
    (source : PanSemStateFiniteExact 64 F) (target : PanSemStateFiniteExact 64 G)
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (region : BitVec 64 → Prop)
    (same : ∀ query, region query → source.memory query = target.memory query)
    (pointer : BitVec 64) (bytes : List (BitVec 8)) :
    ∀ query, region query →
      (@panWriteBytearrayWord8HOL 64 _ pointer bytes source.memory source.memaddrs
        (fun query => Classical.propDecidable (source.memaddrs query)) source.be) query =
      (@panWriteBytearrayWord8HOL 64 _ pointer bytes target.memory target.memaddrs
        (fun query => Classical.propDecidable (target.memaddrs query)) target.be) query := by
  generalize source.memaddrs = leftDomain at *
  generalize target.memaddrs = rightDomain at *
  generalize source.be = leftEndian at *
  generalize target.be = rightEndian at *
  subst rightDomain
  subst rightEndian
  exact write_agrees source.memory target.memory leftDomain leftEndian region same pointer bytes

end InitECandidate.Solver.WitnessRadix.ByteArray

#print axioms InitECandidate.Solver.WitnessRadix.ByteArray.read_congr
#print axioms InitECandidate.Solver.WitnessRadix.ByteArray.read_word8_of_cell
#print axioms InitECandidate.Solver.WitnessRadix.ByteArray.read_of_cells
#print axioms InitECandidate.Solver.WitnessRadix.ByteArray.write_agrees
#print axioms InitECandidate.Solver.WitnessRadix.ByteArray.write_of_cells
