import InitE.SourceSemantics
import Mathlib.Data.List.Basic

namespace InitECandidate.Solver.WitnessRadix.Keccak
open Flapjack Flapjack.Basis.Pure.MlString

def answer (bytes : List (BitVec 8)) : List (BitVec 8) :=
  (Guest.leBytesOfWords (RiscvZkvm.Rv64.Accel.keccakF (Guest.wordsOfLeBytes (bytes.map bitsToByte)))).map byteToBits

theorem packed_length (words : List Guest.Word) : (Guest.leBytesOfWords words).length = 8 * words.length := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    simp only [Guest.leBytesOfWords, List.flatMap_cons, List.length_append] at ih ⊢
    simp only [Guest.leBytes, List.length_map, List.length_range, List.length_cons]
    omega

theorem answer_length (bytes : List (BitVec 8)) : (answer bytes).length = 200 := by
  rw [answer, List.length_map, packed_length, RiscvZkvm.Rv64.Accel.keccakF_length]

/-- The actual fixed source oracle always returns the 200-byte Keccak-f
state for a correctly sized call, with unchanged host memory. -/
theorem oracle (host : Guest.HostMemory) (bytes : List (BitVec 8)) (length : bytes.length = 200) :
    InitE.sourceOracle (.extCall (ofString "keccakf")) host [] bytes = .ret host (answer bytes) := by
  simp [InitE.sourceOracle, Guest.guestOracle, Guest.acceleratorBytes, Guest.keccakfBytes,
    Guest.exactWords, List.length_map, length, answer, ofString, toStringOfBytes]

end InitECandidate.Solver.WitnessRadix.Keccak

#print axioms InitECandidate.Solver.WitnessRadix.Keccak.answer_length
#print axioms InitECandidate.Solver.WitnessRadix.Keccak.oracle
