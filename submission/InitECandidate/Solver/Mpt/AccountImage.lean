import InitECandidate.Solver.Mpt.AccountFieldView
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack PanSemStateFiniteExact

/-- Current physical account object and its two real32-byte references.
Nonce/balance words are read from the mapped56-byte object; their contents
remain unrestricted for runtime accounting. -/
structure Image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out : BitVec 64) where
  output : Output out
  domain : source.memaddrs=InitE.ordinaryDomain
  root : BitVec 64
  hash : BitVec 64
  rootStored : source.memory (out+40#64)=.word root
  hashStored : source.memory (out+48#64)=.word hash
  rootArena : WitnessRadix.AllocatedBytes.Arena root 32
  hashArena : WitnessRadix.AllocatedBytes.Arena hash 32

def Image.of_agreement (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (out : BitVec 64)
    (image : Image source out) (domain : target.memaddrs=source.memaddrs)
    (root : target.memory (out+40#64)=source.memory (out+40#64)) (hash : target.memory (out+48#64)=source.memory (out+48#64)) : Image target out :=
  ⟨image.output,domain.trans image.domain,image.root,image.hash,root.trans image.rootStored,hash.trans image.hashStored,image.rootArena,image.hashArena⟩

/-- Every actual selected item and its returned bounded payload lie in the
current owned ordinary input interval. The array's real heap-end bound and
current scratch/input separation derive the payload's physical byte arena. -/
theorem FieldsView.payload_arena (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer length cursor limit out : BitVec 64) (cutoff : Nat) (items : List Rlp.ListItem)
    (view : FieldsView source array pointer length cursor limit out cutoff items) (arrayBound : array.toNat≤33806089496)
    (index : Nat) (item : Rlp.ListItem) (selected : items[index]?=some item) (header payload : BitVec 64)
    (bounded : header.toNat+payload.toNat≤item.total.toNat) :
    WitnessRadix.AllocatedBytes.Arena (Rlp.Slices.itemPointer pointer items index+header) payload.toNat := by
  obtain ⟨offset,path,inside,valid,encoded⟩ := Rlp.ListItems.at source pointer length.toNat items view.itemsModel index item selected
  have extent : item.size<2^64 := by have := length.isLt; omega
  have totalNumber : item.total.toNat=item.size := by rw [item.total_eq_size,BitVec.toNat_ofNat,Nat.mod_eq_of_lt extent]
  have offsetSmall : offset<2^64 := by have := length.isLt; omega
  have pointerNumber : (Rlp.Slices.itemPointer pointer items index).toNat=pointer.toNat+offset := by
    rw [path,BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt offsetSmall]; have := view.inputFits; omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt offsetSmall]
  rw [totalNumber] at bounded
  have payloadNumber : (Rlp.Slices.itemPointer pointer items index+header).toNat=pointer.toNat+offset+header.toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [pointerNumber]; have := view.inputFits; omega),pointerNumber]
  constructor
  · rw [payloadNumber]
    have := view.arena.lower
    have := view.arena.ordered
    have := view.scratchBelow
    have := view.inputAbove
    omega
  · rw [payloadNumber]
    have := view.inputBefore
    omega

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Image.of_agreement
#print axioms InitECandidate.Solver.Mpt.AccountDecode.FieldsView.payload_arena
