import InitECandidate.Solver.Mpt.WitnessDecodeNormalFrame
import InitECandidate.Solver.Mpt.CompactToNibblesSnapshot
import InitECandidate.Solver.Rlp.SlicesSnapshot

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem slices_snapshot_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit count : BitVec 64) (items : List Rlp.ListItem)
    (snapshot : Rlp.Slices.Snapshot source target pointer length heap cursor limit count items) : NormalFrame source target heap cursor limit :=
  ⟨⟨_,snapshot.heapCell,snapshot.nextArena,snapshot.nextAligned,by have grows:=snapshot.grows; omega⟩,
    ⟨cursor,snapshot.arena,Nat.le_refl _⟩,snapshot.domain,snapshot.endian,snapshot.code,
    fun key notHeap notScratch=>snapshot.globals key notHeap,
    fun query above below=>snapshot.memory query above (Or.inl below)⟩

theorem compact_snapshot_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (length : Nat) (heap cursor limit : BitVec 64) (nibbles : Nat) (leaf : BitVec 64)
    (snapshot : CompactToNibbles.Snapshot source target length heap cursor limit nibbles leaf) : NormalFrame source target heap cursor limit := by
  have domain:=congrArg PanSemStateFiniteExact.memaddrs snapshot.metadata
  change target.memaddrs=source.memaddrs at domain
  have endian:=congrArg PanSemStateFiniteExact.be snapshot.metadata
  change target.be=source.be at endian
  have codeEq:=congrArg PanSemStateFiniteExact.code snapshot.metadata
  change target.code=source.code at codeEq
  have globals:=congrArg PanSemStateFiniteExact.globals snapshot.metadata
  change target.globals=(PersistentAlloc.post source heap (BitVec.ofNat 64 (2*length))).globals at globals
  refine ⟨⟨_,snapshot.heapCell,snapshot.nextArena,snapshot.nextAligned,by have grows:=snapshot.grows; omega⟩,
    ⟨cursor,snapshot.arena,Nat.le_refl _⟩,domain,endian,codeEq,?_,fun query above below=>snapshot.memory query (Or.inl below)⟩
  intro key notHeap notScratch
  rw [globals]
  simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm notHeap]

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.slices_snapshot_frame
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.compact_snapshot_frame
