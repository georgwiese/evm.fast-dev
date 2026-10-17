import InitECandidate.Solver.WitnessRadix.Compact

/-! The implementation branches on a byte load shifted by bit%8. This bridge
instantiates the index directly on 32-byte arrays, avoiding any cryptographic
property or assumed agreement between byte order and a packed hash integer. -/
namespace InitECandidate.Solver.WitnessRadix.ByteKeys
open InitECandidate.Solver.WitnessRadix

abbrev Key := Fin 32 → BitVec 8

/-- Least-significant-bit first within each successive byte, as in the actual
Pancake expression `((ld8 (key + (bit >>> 3))) >>> (bit & 7)) & 1`. -/
def bit (key : Key) (position : Nat) : Bool :=
  (key (Fin.ofNat 32 (position / 8))).getLsbD (position % 8)

theorem byte_index (position : Nat) (inside : position < 256) :
    (Fin.ofNat 32 (position / 8)).val = position / 8 := by
  change (position / 8) % 32 = position / 8
  apply Nat.mod_eq_of_lt
  omega

/-- Inspecting all 256 implementation bits separates all 32-byte keys. -/
theorem separates (left right : Key)
    (same : ∀ position < 256, bit left position = bit right position) : left = right := by
  funext byte
  apply BitVec.eq_of_getLsbD_eq
  intro digit digitInside
  have positionInside : 8 * byte.val + digit < 256 := by have := byte.isLt; omega
  have div : (8 * byte.val + digit) / 8 = byte.val := by omega
  have rem : (8 * byte.val + digit) % 8 = digit := by omega
  have index : Fin.ofNat 32 ((8 * byte.val + digit) / 8) = byte := by
    apply Fin.ext
    rw [byte_index _ positionInside, div]
  have agreed := same (8 * byte.val + digit) positionInside
  simpa only [bit, index, rem] using agreed

def keyAt (readByte : BitVec 64 → BitVec 8) (pointer : BitVec 64) : Key :=
  fun offset => readByte (pointer + BitVec.ofNat 64 offset.val)

theorem bit_at (readByte : BitVec 64 → BitVec 8) (pointer : BitVec 64)
    (position : Nat) (inside : position < 256) :
    bit (keyAt readByte pointer) position =
      (readByte (pointer + BitVec.ofNat 64 (position / 8))).getLsbD (position % 8) := by
  simp only [bit, keyAt, byte_index position inside]

/-- Byte-array instantiation of the duplicate-preserving dictionary theorem. -/
theorem lookup (input : List (Key × Value)) (query : Key) :
    letI : DecidableEq Key := Classical.decEq Key
    fastLookup bit query (buildIndex bit 256 input) = lastValue query input := by
  classical
  exact fastLookup_buildIndex bit 256 separates input query

theorem query_visits (input : List (Key × Value)) (query : Key) :
    queryVisits bit query (buildIndex bit 256 input) ≤ 257 := by
  classical
  exact queryVisits_buildIndex bit 256 input query

end InitECandidate.Solver.WitnessRadix.ByteKeys

#print axioms InitECandidate.Solver.WitnessRadix.ByteKeys.separates
#print axioms InitECandidate.Solver.WitnessRadix.ByteKeys.bit_at
#print axioms InitECandidate.Solver.WitnessRadix.ByteKeys.lookup
#print axioms InitECandidate.Solver.WitnessRadix.ByteKeys.query_visits
