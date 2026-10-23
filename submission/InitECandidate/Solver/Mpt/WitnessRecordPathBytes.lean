import InitECandidate.Solver.Mpt.WitnessDecodeResultNibbles
import InitECandidate.Solver.Mpt.WitnessCorePush
import InitECandidate.Solver.Mpt.WitnessCoreLoopFields

namespace InitECandidate.Solver.Mpt.WitnessRecord
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The genuine PREV link is in scratch, below every pending path's
backing words. The actual push therefore preserves all its path bytes. -/
theorem Payload.PathBytes.pushed (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db previous : BitVec 64) (data : Description) (view : View source record db data)
    (bytes : data.payload.PathBytes source) :
    data.payload.PathBytes (WitnessCore.pushed source record previous data.payload) := by
  cases payloadEq : data.payload with
  | branch node index occupied=>trivial
  | extension pointer length=>
    have current : TrieWalk.NibbleSpan source.memory source.memaddrs source.be pointer length.toNat ∧ pointer.toNat%8=0:=by
      simpa only [Payload.PathBytes,payloadEq] using bytes
    change TrieWalk.NibbleSpan (WitnessCore.pushed source record previous data.payload).memory
      (WitnessCore.pushed source record previous data.payload).memaddrs (WitnessCore.pushed source record previous data.payload).be pointer length.toNat ∧ pointer.toNat%8=0
    refine ⟨current.1.of_agreement source.memory _ source.memaddrs _ source.be _ pointer length.toNat rfl rfl ?_,current.2⟩
    intro offset inside
    have floor:=view.payloadFloor
    simp only [payloadEq,Payload.startAddress] at floor
    have ceiling:=view.ceiling
    have number:=byteAddress_toNat pointer offset (by have fits:=current.1.fits; omega)
    have away : panByteAlignHOL (width:=64) (byteAddress pointer offset)≠record:=by
      intro same
      have equal:=congrArg BitVec.toNat same
      rw [AllocatedBytes.aligned_number,number] at equal
      omega
    change StoreWord.put source.memory record previous (panByteAlignHOL (width:=64) (byteAddress pointer offset))=_
    simp only [StoreWord.put,if_neg away]

/-- The genuine database-band frame protects a pending extension buffer
while a child is decoded or resolved at the evolving real heap. -/
theorem Payload.PathBytes.database_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db heap : BitVec 64) (data : Description) (view : View source record db data)
    (bytes : data.payload.PathBytes source) (before : data.BeforeHeap heap.toNat)
    (frame : WitnessCore.DatabaseFrame source target heap) : data.payload.PathBytes target := by
  cases payloadEq : data.payload with
  | branch node index occupied=>trivial
  | extension pointer length=>
    have current : TrieWalk.NibbleSpan source.memory source.memaddrs source.be pointer length.toNat ∧ pointer.toNat%8=0:=by
      simpa only [Payload.PathBytes,payloadEq] using bytes
    have floor:=view.payloadFloor
    simp only [payloadEq,Payload.startAddress] at floor
    have upper:=before.2
    simp only [payloadEq,Payload.endAddress] at upper
    exact ⟨current.1.of_band source target pointer length.toNat 2713717616 heap.toNat current.2 (by omega) upper frame.domain frame.endian frame.memory,current.2⟩

end InitECandidate.Solver.Mpt.WitnessRecord

#print axioms InitECandidate.Solver.Mpt.WitnessRecord.Payload.PathBytes.pushed
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.Payload.PathBytes.database_frame
