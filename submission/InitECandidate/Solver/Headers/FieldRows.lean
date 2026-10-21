import InitECandidate.Solver.Headers.FieldCost
import InitECandidate.Solver.Rlp.ListItemAt
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Headers.Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Evaluate the two literal loads used by all three original field helpers. -/
theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array index pointer length : BitVec 64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (pointerMapped : source.memaddrs (Rlp.Slices.row array index))
    (lengthMapped : source.memaddrs (Rlp.Slices.row array index+8#64))
    (pointerWord : source.memory (Rlp.Slices.row array index)=.word pointer)
    (lengthWord : source.memory (Rlp.Slices.row array index+8#64)=.word length) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Rlp.Header.values pointer length) := by
  simp only [Rlp.Slices.row,BitVec.add_assoc] at pointerMapped lengthMapped pointerWord lengthWord
  simp [arguments,rowExpression,rowLengthExpression,Rlp.Header.values,Rlp.Slices.row,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,
    arrayCell,indexCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,memLoadHOLExact,isWfShapeExactHOL,
    pointerMapped,lengthMapped,pointerWord,lengthWord,BitVec.add_assoc]

/-- Select the original row from the actually constructed RLP slice array.
The selected pointer and length come from its real records and ordered input. -/
theorem selected_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array pointer : BitVec 64)
    (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (selected : items[index]?=some item) (model : Rlp.ListItems source pointer bytes items)
    (records : Rlp.Slices.Records source.memory array pointer items)
    (domain : source.memaddrs=InitE.ordinaryDomain) (allocation : AllocatedBytes.Arena array (16*items.length))
    (arrayAligned : array.toNat%8=0) (fits : pointer.toNat+bytes<2^64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some (Rlp.Header.values (Rlp.Slices.itemPointer pointer items index) item.total) ∧
      1≤item.total.toNat ∧ item.total.toNat≤bytes ∧ (Rlp.Slices.itemPointer pointer items index).toNat+item.total.toNat<2^64 := by
  have inside : index<items.length := (List.getElem?_eq_some_iff.mp selected).choose
  have rowEq : Rlp.Slices.row array (BitVec.ofNat 64 index)=byteAddress array (16*index) := by
    simp [Rlp.Slices.row,byteAddress,BitVec.ofNat_mul,Nat.mul_comm]
  have lengthEq : Rlp.Slices.row array (BitVec.ofNat 64 index)+8#64=byteAddress array (16*index+8) := by
    rw [rowEq]
    simp only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc]
  have mapped := AllocatedBytes.word_mapped source array (16*items.length) (16*index) domain allocation (by omega) arrayAligned (by omega)
  have mappedLength := AllocatedBytes.word_mapped source array (16*items.length) (16*index+8) domain allocation (by omega) arrayAligned (by omega)
  have cells := Rlp.Slices.Records.at source.memory array pointer items records index item selected
  change source.memory (byteAddress array (16*index))=_ ∧ source.memory (byteAddress array (16*index)+8#64)=_ at cells
  have args := arguments_read source array (BitVec.ofNat 64 index) (Rlp.Slices.itemPointer pointer items index) item.total arrayCell indexCell
    (by rw [rowEq]; exact mapped) (by rw [lengthEq]; exact mappedLength)
    (by rw [rowEq]; exact cells.1) (by rw [rowEq]; exact cells.2)
  have span := model.at_span source pointer bytes items index item selected fits
  exact ⟨args,span.2.1,span.2.2.1,span.2.2.2⟩

/-- A complete original field helper is linear in the actual selected row;
its row also has the enclosing header's real byte bound. -/
theorem selected_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer cursor limit : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (selected : items[index]?=some item) (model : Rlp.ListItems source pointer bytes items)
    (records : Rlp.Slices.Records source.memory array pointer items)
    (arena : Rlp.Validation.Arena source cursor limit) (allocation : AllocatedBytes.Arena array (16*items.length))
    (arrayAligned : array.toNat%8=0) (fits : pointer.toNat+bytes<2^64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source kind.body).2.clock≤60*item.total.toNat+42 ∧
      source.clock-(evaluateHOLFiniteState source kind.body).2.clock≤60*bytes+42 := by
  obtain ⟨args,positive,bounded,itemFits⟩ := selected_arguments source array pointer bytes index items item selected model records arena.domain allocation arrayAligned fits arrayCell indexCell
  have price := body_cost source kind (Rlp.Slices.itemPointer pointer items index) item.total cursor limit args arena itemFits installed
  exact ⟨price,price.trans (by omega)⟩

end InitECandidate.Solver.Headers.Field

#print axioms InitECandidate.Solver.Headers.Field.arguments_read
#print axioms InitECandidate.Solver.Headers.Field.selected_arguments
#print axioms InitECandidate.Solver.Headers.Field.selected_body_cost
