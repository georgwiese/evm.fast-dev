import InitECandidate.Solver.Input.HeapFrame
import InitECandidate.Solver.Input.ScalarStoreMemory

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix WitnessRadix.QueryBranch

/-- Only the physical backing words of copied bytes must agree. -/
theorem HeapInput.of_words (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (pointer : BitVec 64) (image : HeapInput source input pointer)
    (domain : target.memaddrs = source.memaddrs) (endian : target.be = source.be)
    (frame : ∀ offset < input.length % 2^64,
      target.memory (panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 offset)) =
        source.memory (panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 offset))) : HeapInput target input pointer := by
  classical
  intro offset inside
  have old := image offset inside
  have same := congrArg (fun value : HolWordLab 64 => match value with
    | .word word => if source.memaddrs (panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 offset))
      then some (panGetByteHOL (pointer + BitVec.ofNat 64 offset) word source.be) else none) (frame offset inside)
  change @panMemLoadByteHOL 64 _ target.memory target.memaddrs _ target.be _ = _
  unfold panMemLoadByteHOL
  rw [domain, endian]
  exact same.trans old

/-- A real continuing scalar-operation store preserves copied input when
its destination word is before or beyond the copied extent. Actual value reads
and mapping success are conclusions of that store, not caller assumptions. -/
theorem HeapInput.op_store_separate (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (pointer address : BitVec 64) (destination : ExpHOL 64) (operation : BinOp) (arguments : List (ExpHOL 64))
    (image : HeapInput source input pointer) (aligned : pointer.toNat % 8 = 0)
    (fits : pointer.toNat + input.length % 2^64 < 2^64)
    (separate : address.toNat < pointer.toNat ∨ pointer.toNat + input.length % 2^64 ≤ address.toNat)
    (read : eval source destination = some (.val (.word address)))
    (actual : evaluateHOLFiniteState source (.store destination (.op operation arguments)) = (none, target)) : HeapInput target input pointer := by
  obtain ⟨value, memory, evaluated, stored, targetEq⟩ := store_at_normal source target destination (.op operation arguments) address read actual
  apply HeapInput.of_words source target input pointer image (by rw [targetEq]) (by rw [targetEq])
  intro offset inside
  apply MemoryAt.op_store_normal source target destination operation arguments address _ read _ actual
  intro same
  have number := MemoryBytes.offset_toNat pointer offset (by omega)
  have cellNumber := AllocatedBytes.aligned_number (pointer + BitVec.ofNat 64 offset)
  have equal := congrArg BitVec.toNat same
  rw [cellNumber, number] at equal
  rcases separate with before | after <;> omega

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.HeapInput.of_words
#print axioms InitECandidate.Solver.Input.Blob.HeapInput.op_store_separate
