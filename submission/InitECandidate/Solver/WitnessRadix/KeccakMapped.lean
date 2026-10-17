import InitECandidate.Solver.WitnessRadix.KeccakFfi
import InitECandidate.Solver.WitnessRadix.ByteArrayFrame

namespace InitECandidate.Solver.WitnessRadix.Keccak
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete literal Keccak-f function from mapped aligned state cells and
the real fixed oracle; no successful read or foreign execution is assumed. -/
theorem f1600_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (stpLocal : source.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (aligned : pointer.toNat % 8 = 0) (fits : pointer.toNat + 200 < 2 ^ 64)
    (mapped : ∀ word : Fin 25, source.memaddrs (byteAddress pointer (8 * word.val))) :
    ∃ bytes : List (BitVec 8), bytes.length = 200 ∧
      evaluateHOLFiniteState source f1600Body =
        (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite (post source pointer bytes)) := by
  obtain ⟨bytes, readArray, length⟩ := ByteArray.read200 source pointer aligned fits mapped
  exact ⟨bytes, length, f1600_execute source pointer bytes stpLocal oracleEq readArray⟩

theorem post_memory_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (bytes : List (BitVec 8))
    (away : ∀ offset < 200, query ≠ panByteAlignHOL (width := 64) (byteAddress pointer offset)) :
    (post source pointer bytes).memory query = source.memory query := by
  apply ByteArray.write_away
  intro offset inside
  exact away offset (by rw [answer_length] at inside; exact inside)

end InitECandidate.Solver.WitnessRadix.Keccak

#print axioms InitECandidate.Solver.WitnessRadix.Keccak.f1600_mapped
#print axioms InitECandidate.Solver.WitnessRadix.Keccak.post_memory_away
