import InitECandidate.Solver.Input.VarList.ArrayGeometry
import InitECandidate.Solver.WitnessRadix.Keccak256Allocated

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes

/-- Decoder evidence supplies each actual hash-input arena. The fixed state,
padding and digest arenas remain startup/global-allocation obligations. -/
theorem Records.hash_buffers (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length : Nat) (records : Records source input pointer array start length)
    (stp pad out : BitVec 64) (stateArena : Arena stp 200) (stateAligned : stp.toNat%8=0)
    (paddingArena : Arena pad 136) (paddingAligned : pad.toNat%8=0) (outputArena : Arena out 32) :
    ∀ index<decodedCount input start length,
      Keccak256.Buffers stp (recordPointer input pointer start index) pad out
        (recordLength input start length (decodedCount input start length) index).toNat := by
  intro index inside
  exact ⟨stateArena,stateAligned,(records.slice_geometry source input pointer array start length index inside).2.2.1,
    paddingArena,paddingAligned,outputArena⟩

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.Records.hash_buffers
