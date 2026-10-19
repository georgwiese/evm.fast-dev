import InitECandidate.Solver.Input.RlpWrite.U256Value
import InitECandidate.Solver.WitnessRadix.MemoryBytes

namespace InitECandidate.Solver.Input.RlpWrite.U256Value
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

def memoryWords (source : PanSemStateFiniteExact 64 Guest.HostMemory) (address : BitVec 64) : Words :=
  fun index => WitnessRadix.MemoryBytes.wordBits (source.memory (address + BitVec.ofNat 64 (8 * index.val)))

theorem load (source : PanSemStateFiniteExact 64 Guest.HostMemory) (expression : ExpHOL 64) (address : BitVec 64)
    (read : eval source expression = some (.val (.word address)))
    (mapped : ∀ index : Fin 4, source.memaddrs (address + BitVec.ofNat 64 (8 * index.val))) :
    eval source (.load tupleShape expression) = some (tuple (memoryWords source address)) := by
  classical
  have stored (index : Fin 4) : source.memory (address + BitVec.ofNat 64 (8 * index.val)) =
      .word (memoryWords source address index) := by
    cases cell : source.memory (address + BitVec.ofNat 64 (8 * index.val)) with
    | word word => simp [memoryWords, WitnessRadix.MemoryBytes.wordBits, cell]
  have m0 : source.memaddrs address := by simpa using mapped 0
  have m1 : source.memaddrs (address + 8#64) := mapped 1
  have m2 : source.memaddrs (address + 16#64) := mapped 2
  have m3 : source.memaddrs (address + 24#64) := mapped 3
  have s0 : source.memory address = .word (memoryWords source address 0) := by simpa using stored 0
  have s1 : source.memory (address + 8#64) = .word (memoryWords source address 1) := stored 1
  have s2 : source.memory (address + 16#64) = .word (memoryWords source address 2) := stored 2
  have s3 : source.memory (address + 24#64) = .word (memoryWords source address 3) := stored 3
  simp [eval, evalHOLExact, tupleShape, tuple, isWfShapeExactHOL, isWfShapesExactHOL,
    memLoadHOLExact, memLoadsHOLExact, bytesInWordHOL, sizeOfShapeWithContextHOL,
    show evalHOLExact (toExact source) expression = some (.val (.word address)) from read,
    BitVec.add_assoc, m0, m1, m2, m3, s0, s1, s2, s3]

end InitECandidate.Solver.Input.RlpWrite.U256Value

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Value.load
