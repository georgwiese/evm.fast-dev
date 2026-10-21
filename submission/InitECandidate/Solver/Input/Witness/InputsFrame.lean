import InitECandidate.Solver.Input.Witness.Inputs
import InitECandidate.Solver.Input.HashInputDataFrame

namespace InitECandidate.Solver.Input.Witness
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Actual witness data survives hash/constructor writes outside the fixed
input frontier. Its decoder allocation snapshot stays a pure address fact. -/
theorem Inputs.of_frame (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array si codeArray headerArray frontier : BitVec 64) (start first middle last total lower upper : Nat)
    (actual : Inputs origin input pointer array si codeArray headerArray frontier start first middle last total)
    (frame : HashInput.Frame origin current lower upper) (domain : current.memaddrs=origin.memaddrs) (endian : current.be=origin.be)
    (aligned : pointer.toNat%8=0) (fits : pointer.toNat+input.length%2^64<2^64)
    (inputAfter : lower≤pointer.toNat) (inputBefore : pointer.toNat+input.length%2^64≤upper)
    (arrayAfter : lower≤array.toNat) (frontierBefore : frontier.toNat≤upper)
    (siArena : AllocatedBytes.Arena si 96) (siAfter : lower≤si.toNat) (siBefore : si.toNat+96≤upper) :
    Inputs current input pointer array si codeArray headerArray frontier start first middle last total := by
  have cell (offset : Nat) (inside : offset<96) : current.memory (byteAddress si offset)=origin.memory (byteAddress si offset) := by
    have number : (byteAddress si offset).toNat=si.toNat+offset := byteAddress_toNat si offset (by have h:=siArena.upper; omega)
    exact frame.words _ (by rw [number]; omega) (by rw [number]; omega)
  have nodes := frame.records origin current input pointer array (start+first) (middle-first) lower upper actual.nodes arrayAfter
    (by have h:=actual.finalAddress; omega)
  have codes := frame.records origin current input pointer codeArray (start+middle) (last-middle) lower upper actual.codes
    (by have h:=actual.codeAddress; omega) (by have a:=actual.codeAddress; have b:=actual.finalAddress; omega)
  have headers := frame.records origin current input pointer headerArray (start+last) (total-last) lower upper actual.headers
    (by have a:=actual.codeAddress; have b:=actual.headerAddress; omega)
    (by have a:=actual.codeAddress; have b:=actual.headerAddress; have c:=actual.finalAddress; omega)
  exact ⟨nodes,codes,headers,actual.nodeSizes,actual.codeSizes,actual.headerCount,
    frame.heap_input origin current input pointer lower upper actual.bytes domain endian aligned fits inputAfter inputBefore,
    (cell 40 (by decide)).trans actual.nodePointer,(cell 48 (by decide)).trans actual.nodeCount,
    (cell 56 (by decide)).trans actual.codePointer,(cell 64 (by decide)).trans actual.codeCount,
    (cell 72 (by decide)).trans actual.headerPointer,(cell 80 (by decide)).trans actual.headerCountCell,
    actual.codeAddress,actual.headerAddress,actual.codeAligned,actual.headerAligned,actual.finalAddress,actual.finalBound,actual.finalAligned⟩

end InitECandidate.Solver.Input.Witness
#print axioms InitECandidate.Solver.Input.Witness.Inputs.of_frame
