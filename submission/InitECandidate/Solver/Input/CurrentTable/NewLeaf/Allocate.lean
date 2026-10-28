import InitECandidate.Solver.Input.CurrentTable.NewLeaf.AfterNode
import InitECandidate.Solver.Input.CurrentTable.NewNode.Context
import InitECandidate.Solver.Input.CurrentTable.ImageFacts

namespace InitECandidate.Solver.Input.CurrentTable.NewLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- The actual node allocator's metadata write protects the earlier query
buffer. The caller must derive this physical order, rather than just a
dictionary invariant. -/
theorem Fields.after_next {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table cap node pos pointer : BitVec 64} {key : KeyBits.Key}
    (fields : Fields source table cap node pos pointer key) (beforeTable : pointer.toNat+32 ≤ table.toNat) :
    Fields (New.putField source table 64 (node+1#64)) table cap node pos pointer key := by
  have preserved (offset : Nat) (small : offset < 88) (different : offset ≠ 64) :
      (New.putField source table 64 (node+1#64)).memory (table+BitVec.ofNat 64 offset) = source.memory (table+BitVec.ofNat 64 offset) := by
    have away := byteAddress_ne table offset 64 (by have := fields.geometry.table.upper; omega)
      (by have := fields.geometry.table.upper; omega) different
    change table+BitVec.ofNat 64 offset ≠ table+64#64 at away
    simp only [New.putField,StoreWord.put,if_neg away]
  have bytes : FirstDiff.ByteView (New.putField source table 64 (node+1#64)) pointer key := by
    apply StoreWord.byteView_away source (table+64#64) (node+1#64) pointer key _ fields.copy.bytes
    intro index same
    have byteNumber := byteAddress_toNat pointer index.val (by have bound := fields.copy.sourceFits; have := index.isLt; omega)
    change (pointer+BitVec.ofNat 64 index.val).toNat = pointer.toNat+index.val at byteNumber
    have backing := AllocatedBytes.aligned_number (pointer+BitVec.ofNat 64 index.val)
    rw [byteNumber] at backing
    have fieldNumber := byteAddress_toNat table 64 (by have := fields.geometry.table.upper; omega)
    change (table+64#64).toNat = table.toNat+64 at fieldNumber
    have sameNumber := congrArg BitVec.toNat same
    rw [backing,fieldNumber] at sameNumber
    have := index.isLt
    omega
  exact ⟨fields.geometry,fields.aligned,fields.inside,fields.posInside,
    (preserved 0 (by decide) (by decide)).trans fields.lengthCell,
    (preserved 8 (by decide) (by decide)).trans fields.strideCell,
    (preserved 24 (by decide) (by decide)).trans fields.countCell,
    (preserved 32 (by decide) (by decide)).trans fields.keysCell,
    (preserved 40 (by decide) (by decide)).trans fields.nodesCell,
    (preserved 48 (by decide) (by decide)).trans fields.orderCell,
    ⟨fields.copy.domain,fields.copy.little,fields.copy.sourceAligned,fields.copy.targetAligned,
      fields.copy.sourceFits,fields.copy.targetArena,fields.copy.ordered,bytes⟩⟩

/-- The reached insertion image supplies every physical field used by the
original new-leaf continuation. Query alignment/order remain explicit
ownership obligations for the real database caller. -/
theorem fields_from_image {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop} (key : KeyBits.Key)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (available : next ≤ cap.toNat) (little : source.be = false) (aligned : pointer.toNat%8 = 0)
    (beforeTable : pointer.toNat+32 ≤ table.toNat) (bytes : FirstDiff.ByteView source pointer key) :
    Fields source table cap (BitVec.ofNat 64 next) (BitVec.ofNat 64 count) pointer key := by
  have nextSmall : next < 2^64 := by have := image.geometry.capacityBound; omega
  have countSmall : count < 2^64 := by have := image.countBound; have := image.geometry.capacityBound; omega
  have nextNumber : (BitVec.ofNat 64 next).toNat = next := by simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt nextSmall]
  have countNumber : (BitVec.ofNat 64 count).toNat = count := by simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt countSmall]
  have inside : (BitVec.ofNat 64 next).toNat ≤ cap.toNat := by rw [nextNumber]; exact available
  refine ⟨image.geometry,image.aligned,inside,?_,?_,image.stride,image.countCell,image.keysCell,image.nodesCell,image.orderCell,?_⟩
  · rw [countNumber]; exact image.countBound
  · simpa using image.keyLength
  · refine ⟨image.domain,little,aligned,slot_aligned _ _ cap 32 image.geometry.keys inside image.geometry.keysAligned (by decide),
      ?_,image.geometry.key_slot _ inside,?_,bytes⟩
    · have := image.geometry.table.upper
      omega
    · rw [slot_number _ _ cap 32 image.geometry.keys inside]
      have := image.geometry.tableBefore
      omega

end InitECandidate.Solver.Input.CurrentTable.NewLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.Fields.after_next
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.fields_from_image
