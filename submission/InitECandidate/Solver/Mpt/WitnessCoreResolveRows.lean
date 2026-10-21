import InitECandidate.Solver.Mpt.WitnessCoreResolveProgram
import InitECandidate.Solver.Mpt.WitnessRecordView

namespace InitECandidate.Solver.Mpt.WitnessRecord
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def Payload.slotIndex : Payload→Nat | .extension ..=>1 | .branch _ index _=>index.val

theorem Payload.slot_bound (payload : Payload) : payload.slotIndex<payload.count := by
  cases payload with
  | extension nibbles length=>change 1<2; decide
  | branch node index occupied=>have inside:=index.isLt; simp only [Payload.slotIndex,Payload.count]; omega

theorem View.array (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db : BitVec 64)
    (data : Description) (view : View source record db data) : source.memory (record+24#64)=.word data.array := by
  have member : (24,data.array)∈data.cells:=by
    cases payloadEq : data.payload <;> simp [Description.cells,payloadEq]
  exact view.cells _ member

end InitECandidate.Solver.Mpt.WitnessRecord

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem resolve_array_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db : BitVec 64) (data : WitnessRecord.Description) (view : WitnessRecord.View source record db data)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record))) :
    eval source resolveArray=some (.val (.word data.array)) := by
  have mapped : source.memaddrs (record+24#64):=by
    simpa only [byteAddress] using view.mapped source record db data 24 (by decide) (by decide)
  have stored:=view.array source record db data
  simp [eval,resolveArray,evalHOLExact,evalListHOLExact,localVar,toExact,topCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,stored]

/-- The actual dynamic slot loads use the current physical row array.
The selected original row supplies the two bounded input words, without
assuming successful parsing or any contents of the input bytes. -/
theorem resolve_arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer db : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem)
    (rows : WitnessDecode.Rows source array pointer bytes items) (item : Rlp.ListItem)
    (selected : items[index]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 index))))
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) resolveArguments=
      some [.val (.word db),.val (.word (Rlp.Slices.itemPointer pointer items index)),.val (.word item.total)] := by
  have inside : index<items.length:=(List.getElem?_eq_some_iff.mp selected).choose
  have mapped:=AllocatedBytes.word_mapped source array (16*items.length) (16*index) rows.domain rows.allocation (by omega) rows.aligned (by omega)
  have lengthMapped:=AllocatedBytes.word_mapped source array (16*items.length) (16*index+8) rows.domain rows.allocation (by omega) rows.aligned (by omega)
  have cells:=Rlp.Slices.Records.at source.memory array pointer items rows.records index item selected
  change source.memaddrs (array+BitVec.ofNat 64 (16*index)) at mapped
  have lengthAddress : byteAddress array (16*index+8)=array+BitVec.ofNat 64 (16*index)+8#64:=by
    simp only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc]
  rw [lengthAddress] at lengthMapped
  have product : BitVec.ofNat 64 index*16#64=BitVec.ofNat 64 (16*index):=by
    rw [←BitVec.ofNat_mul]
    congr 1
    omega
  simp only [BitVec.add_assoc] at lengthMapped cells
  simp [resolveArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,
    arrayCell,slotCell,dbCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,memLoadHOLExact,isWfShapeExactHOL,
    product,mapped,lengthMapped,cells.1,cells.2]

/-- A live record in resolve mode selects a genuine bounded input row.
All local bindings are those reached by the original arr declaration. -/
theorem resolve_row (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db : BitVec 64) (data : WitnessRecord.Description) (view : WitnessRecord.View source record db data)
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 data.payload.slotIndex))))
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db))) :
    ∃ item : Rlp.ListItem,
      data.items[data.payload.slotIndex]?=some item ∧
      evalListHOLFinite (QueryBranch.bind source "arr" data.array)
        (h:=fun query=>Classical.propDecidable ((QueryBranch.bind source "arr" data.array).memaddrs query)) resolveArguments=
        some [.val (.word db),.val (.word (Rlp.Slices.itemPointer data.listPointer data.items data.payload.slotIndex)),.val (.word item.total)] ∧
      1≤item.total.toNat ∧ item.total.toNat≤data.bytes ∧ item.total.toNat≤1024 ∧
      2713731432≤(Rlp.Slices.itemPointer data.listPointer data.items data.payload.slotIndex).toNat ∧
      (Rlp.Slices.itemPointer data.listPointer data.items data.payload.slotIndex).toNat+item.total.toNat≤db.toNat := by
  have inside : data.payload.slotIndex<data.items.length:=by rw [view.count]; exact data.payload.slot_bound
  let item:=data.items[data.payload.slotIndex]
  have selected : data.items[data.payload.slotIndex]?=some item:=by simp [item,inside]
  let ready:=QueryBranch.bind source "arr" data.array
  have rows:=view.rows.frame source ready data.array data.listPointer data.bytes data.items rfl (by intros; rfl)
  have slot : ready.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 data.payload.slotIndex))):=
    (bind_lookup_other source "arr" "slot" data.array (by decide)).trans slotCell
  have dbLocal : ready.locals.lookup (ofString "db")=some (.val (.word db)):=
    (bind_lookup_other source "arr" "db" data.array (by decide)).trans dbCell
  have args:=resolve_arguments_read ready data.array data.listPointer db data.bytes data.payload.slotIndex data.items rows item selected
    (bind_lookup_same _ _ _) slot dbLocal
  obtain ⟨positive,small,lower,upper⟩:=view.rows.intervals _ _ selected
  have parentSmall:=view.parentBound
  have parentLower:=view.parentLower
  have beforeDb:=view.parentBeforeDb
  have payloadLower:=view.payloadLower
  have payloadUpper:=view.payloadUpper
  exact ⟨item,selected,args,positive,small,by omega,by omega,by omega⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessRecord.Payload.slot_bound
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.View.array
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolve_array_read
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolve_arguments_read
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolve_row
