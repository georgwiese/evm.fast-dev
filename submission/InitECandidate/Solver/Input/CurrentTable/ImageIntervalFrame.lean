import InitECandidate.Solver.Input.CurrentTable.ImageCells
import InitECandidate.Solver.Input.CurrentTable.CellGeometry
import InitECandidate.Solver.Input.HashInputFrame

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem FirstDiff.ByteView.interval_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer : BitVec 64} {key : KeyBits.Key} (lower upper : Nat)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : HashInput.Frame source target lower upper)
    (fits : pointer.toNat+32<2^64) (aligned : pointer.toNat%8=0)
    (after : lower≤pointer.toNat) (before : pointer.toNat+32≤upper)
    (view : FirstDiff.ByteView source pointer key) : FirstDiff.ByteView target pointer key := by
  intro byte
  have number := byteAddress_toNat pointer byte.val (by have := byte.isLt; omega)
  change (pointer+BitVec.ofNat 64 byte.val).toNat=pointer.toNat+byte.val at number
  have backing := AllocatedBytes.aligned_number (pointer+BitVec.ofNat 64 byte.val)
  rw [number] at backing
  have kept := memory.words (panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 byte.val)) (by omega) (by have := byte.isLt; omega)
  by_cases mapped : source.memaddrs (panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 byte.val))
  all_goals simpa [panMemLoadByteHOL,domain,endian,kept,mapped] using view byte

/-- A finite earlier-memory interval protects the entire real Patricia
image. Later allocations and hashes may change memory beyond this extent. -/
theorem Image.of_interval {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : HashInput.Frame source target table.toNat (New.endPointer table cap).toNat) :
    Image target table cap root next count valid bits left right keys ValueOf := by
  have tableEnd : table.toNat+88≤(New.endPointer table cap).toNat := by
    have a:=image.geometry.tableBefore
    have b:=image.geometry.keysBefore
    have c:=image.geometry.nodesBefore
    have d:=image.geometry.orderBefore
    omega
  apply image.of_cells domain
  · intro offset small
    have number := byteAddress_toNat table offset (by have := image.geometry.table.upper; omega)
    change (table+BitVec.ofNat 64 offset).toNat=table.toNat+offset at number
    exact memory.words _ (by omega) (by omega)
  · intro index member offset small
    have inside := image.node_inside index member
    have number := cell_number (New.nodesPointer table cap) index cap offset image.geometry.nodes inside small
    have low := image.geometry.cell_after_table index inside offset small
    have high := image.geometry.nodesBefore
    have final := image.geometry.orderBefore
    exact memory.words _ (by omega) (by omega)
  · intro index member marked
    have inside := image.node_inside index member
    have number := slot_number (New.keysPointer table) index cap 32 image.geometry.keys inside
    have aligned := slot_aligned (New.keysPointer table) index cap 32 image.geometry.keys inside image.geometry.keysAligned (by decide)
    have after : table.toNat≤(slot (New.keysPointer table) index 32).toNat := by rw [number]; have := image.geometry.tableBefore; omega
    have before : (slot (New.keysPointer table) index 32).toNat+32≤(New.endPointer table cap).toNat := by
      rw [number]
      have a:=image.geometry.keysBefore
      have b:=image.geometry.nodesBefore
      have c:=image.geometry.orderBefore
      omega
    exact FirstDiff.ByteView.interval_frame table.toNat (New.endPointer table cap).toNat domain endian memory
      (image.key_fits index member) aligned after before (image.leafKeys index member marked)

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.ByteView.interval_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.Image.of_interval
