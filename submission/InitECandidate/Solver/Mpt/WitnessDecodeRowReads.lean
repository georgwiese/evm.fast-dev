import InitECandidate.Solver.Mpt.WitnessDecodeProgram
import InitECandidate.Solver.Rlp.ListItemAt
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Both literal row loads in original237 read the actual constructed
array. Their nonwrapping input interval lies inside the enclosing payload;
no speculative item call or later successful memory read is assumed. -/
theorem record_arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (selected : items[index]?=some item) (model : Rlp.ListItems source pointer bytes items)
    (records : Rlp.Slices.Records source.memory array pointer items)
    (domain : source.memaddrs=InitE.ordinaryDomain) (allocation : AllocatedBytes.Arena array (16*items.length))
    (arrayAligned : array.toNat%8=0) (fits : pointer.toNat+bytes<2^64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (recordArguments index)=
      some (Rlp.Header.values (Rlp.Slices.itemPointer pointer items index) item.total) ∧
      1≤item.total.toNat ∧ item.total.toNat≤bytes ∧
      pointer.toNat≤(Rlp.Slices.itemPointer pointer items index).toNat ∧
      (Rlp.Slices.itemPointer pointer items index).toNat+item.total.toNat≤pointer.toNat+bytes := by
  have inside : index<items.length:=(List.getElem?_eq_some_iff.mp selected).choose
  have mapped:=AllocatedBytes.word_mapped source array (16*items.length) (16*index) domain allocation (by omega) arrayAligned (by omega)
  have lengthMapped:=AllocatedBytes.word_mapped source array (16*items.length) (16*index+8) domain allocation (by omega) arrayAligned (by omega)
  have cells:=Rlp.Slices.Records.at source.memory array pointer items records index item selected
  change source.memaddrs (array+BitVec.ofNat 64 (16*index)) at mapped
  have lengthAddress : byteAddress array (16*index+8)=array+BitVec.ofNat 64 (16*index)+8#64:=by
    simp only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc]
  rw [lengthAddress] at lengthMapped
  have product : BitVec.ofNat 64 index*16#64=BitVec.ofNat 64 (16*index):=by
    rw [←BitVec.ofNat_mul]
    congr 1
    omega
  simp only [BitVec.add_assoc] at lengthMapped cells
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (recordArguments index)=
      some (Rlp.Header.values (Rlp.Slices.itemPointer pointer items index) item.total):=by
    simp [recordArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,
      arrayCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,memLoadHOLExact,isWfShapeExactHOL,
      product,mapped,lengthMapped,cells.1,cells.2]
  obtain ⟨offset,location,extent,valid,encoded⟩:=model.at source pointer bytes items index item selected
  have span:=model.at_span source pointer bytes items index item selected fits
  have offsetNumber : (BitVec.ofNat 64 offset).toNat=offset:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have pointerNumber : (Rlp.Slices.itemPointer pointer items index).toNat=pointer.toNat+offset:=by
    rw [location,BitVec.toNat_add_of_lt (by rw [offsetNumber]; omega),offsetNumber]
  exact ⟨args,span.2.1,span.2.2.1,by rw [pointerNumber]; omega,by rw [pointerNumber,span.1]; omega⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.record_arguments_read
