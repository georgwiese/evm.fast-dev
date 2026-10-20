import InitECandidate.Solver.Input.WordCodec
import InitECandidate.Solver.WitnessRadix.KeccakOracle

namespace InitECandidate.Solver.Input.WordArrayCodec
open Flapjack

def bits (words : List Guest.Word) : List (BitVec 8) := (Guest.leBytesOfWords words).map byteToBits

theorem length (words : List Guest.Word) : (bits words).length = 8 * words.length := by
  rw [bits,List.length_map,WitnessRadix.Keccak.packed_length]

/-- The actual accelerator word decoder inverts the fixed guest's aligned
little-endian word packing, independently of all word values. -/
theorem words_roundtrip (words : List Guest.Word) : Guest.wordsOfLeBytes (Guest.leBytesOfWords words) = words := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    have front (tail : List UInt8) : Guest.wordsOfLeBytes (Guest.leBytes word ++ tail) =
        Guest.wordOfLeBytes (Guest.leBytes word) :: Guest.wordsOfLeBytes tail := rfl
    change Guest.wordsOfLeBytes (Guest.leBytes word ++ Guest.leBytesOfWords rest) = word :: rest
    rw [front,WordCodec.guest_roundtrip,ih]

theorem bits_roundtrip (words : List Guest.Word) : Guest.wordsOfLeBytes ((bits words).map bitsToByte) = words := by
  simp only [bits,List.map_map,Function.comp_def,bitsToByte_byteToBits,List.map_id',words_roundtrip]

end InitECandidate.Solver.Input.WordArrayCodec

#print axioms InitECandidate.Solver.Input.WordArrayCodec.length
#print axioms InitECandidate.Solver.Input.WordArrayCodec.words_roundtrip
#print axioms InitECandidate.Solver.Input.WordArrayCodec.bits_roundtrip
