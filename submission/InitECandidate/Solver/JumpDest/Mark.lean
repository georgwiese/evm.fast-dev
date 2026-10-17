import InitECandidate.Solver.JumpDest.Reads

namespace InitECandidate.Solver.JumpDest
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def setBit (old index : BitVec 64) : BitVec 64 := old ||| ((1#64 : BitVec 64) <<< ((index &&& 63#64).toNat : Nat))

theorem bit_shift_small (index : BitVec 64) : (index &&& 63#64).toNat < 64 := by
  rw [BitVec.toNat_and]
  have bound : index.toNat &&& 63 ≤ 63 := Nat.and_le_right
  change index.toNat &&& 63 < 64
  omega

/-- The actual JUMPDEST store reads and sets one bitmap word. No other memory
word or local/global/clock field is modified. -/
theorem mark_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (bitmap index old : BitVec 64)
    (bitmapLocal : source.locals.lookup (ofString "bm") = some (.val (.word bitmap)))
    (pcLocal : source.locals.lookup (ofString "pc") = some (.val (.word index)))
    (mapped : source.memaddrs (bitmap + wordOffset index))
    (cell : source.memory (bitmap + wordOffset index) = .word old) :
    evaluateHOLFiniteState source mark =
      (none, {source with memory := WitnessRadix.StoreWord.put source.memory (bitmap + wordOffset index) (setBit old index)}) := by
  have addressRead := bitmap_address_read source bitmap index bitmapLocal pcLocal
  have small := bit_shift_small index
  have valid : ¬ (index.toNat &&& 63 ≠ 0 ∧ 64 ≤ index.toNat &&& 63) := by
    have bound : index.toNat &&& 63 ≤ 63 := Nat.and_le_right
    omega
  have valueRead : eval source bitmapValue = some (.val (.word (setBit old index))) := by
    simp only [wordOffset] at mapped cell
    simp [eval, bitmapValue, bitmapAddress, wordOffset, localVar, evalHOLExact, evalListHOLExact,
      toExact, bitmapLocal, pcLocal, setBit, valueIsWord, valueWord, wordOpHOL, wordOp, wordShiftHOL, panOpHOL,
      valid, AndOp.and, OrOp.or, memLoadHOLExact, isWfShapeExactHOL, mapped, cell]
  exact WitnessRadix.StoreWord.execute source bitmapAddress bitmapValue (bitmap + wordOffset index)
    (setBit old index) addressRead valueRead mapped

/-- The bitmap store is strictly below a protected earlier allocation when
its reserved range lies below that allocation. No hash or bytecode-content
assumption is used. -/
theorem word_below (bitmap index query : BitVec 64) (length : Nat)
    (inside : index.toNat < length) (below : bitmap.toNat + bitmapBytes length ≤ query.toNat) :
    bitmap + wordOffset index ≠ query := by
  have selected := selected_word length index.toNat inside
  have offset := word_offset_number index
  have queryBound := query.isLt
  have fits : bitmap.toNat + (wordOffset index).toNat < 2 ^ 64 := by omega
  have number := BitVec.toNat_add_of_lt fits
  intro equal
  have same := congrArg BitVec.toNat equal
  omega

theorem marked_memory_away (memory : WitnessRadix.WordWrites.Memory) (bitmap index query old : BitVec 64) (length : Nat)
    (inside : index.toNat < length) (below : bitmap.toNat + bitmapBytes length ≤ query.toNat) :
    WitnessRadix.StoreWord.put memory (bitmap + wordOffset index) (setBit old index) query = memory query :=
  if_neg (Ne.symm (word_below bitmap index query length inside below))

/-- Excludes every byte address in one concrete reserved bitmap range. -/
def Outside (bitmap : BitVec 64) (bytes : Nat) (query : BitVec 64) : Prop :=
  ∀ offset < bytes, query ≠ WitnessRadix.byteAddress bitmap offset

theorem outside_above (bitmap query : BitVec 64) (bytes : Nat)
    (above : bitmap.toNat + bytes ≤ query.toNat) : Outside bitmap bytes query := by
  intro offset inside equal
  have number := WitnessRadix.byteAddress_toNat bitmap offset (by have bound := query.isLt; omega)
  have same := congrArg BitVec.toNat equal
  omega

theorem outside_below (bitmap query : BitVec 64) (bytes : Nat)
    (below : query.toNat < bitmap.toNat) (fits : bitmap.toNat + bytes < 2 ^ 64) : Outside bitmap bytes query := by
  intro offset inside equal
  have number := WitnessRadix.byteAddress_toNat bitmap offset (by omega)
  have same := congrArg BitVec.toNat equal
  omega

theorem Outside.selected (bitmap query index : BitVec 64) (length : Nat)
    (outside : Outside bitmap (bitmapBytes length) query) (inside : index.toNat < length) :
    query ≠ bitmap + wordOffset index := by
  have selected := selected_word length index.toNat inside
  have offset := word_offset_number index
  have away := outside (wordOffset index).toNat (by omega)
  simpa [WitnessRadix.byteAddress, BitVec.ofNat_toNat] using away

end InitECandidate.Solver.JumpDest

#print axioms InitECandidate.Solver.JumpDest.bit_shift_small
#print axioms InitECandidate.Solver.JumpDest.mark_execute
#print axioms InitECandidate.Solver.JumpDest.word_below

#print axioms InitECandidate.Solver.JumpDest.marked_memory_away

#print axioms InitECandidate.Solver.JumpDest.outside_above
#print axioms InitECandidate.Solver.JumpDest.outside_below
#print axioms InitECandidate.Solver.JumpDest.Outside.selected
