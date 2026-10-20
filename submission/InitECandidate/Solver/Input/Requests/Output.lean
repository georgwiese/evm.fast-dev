import InitECandidate.Solver.Input.Requests.CountLocals
import InitECandidate.Solver.Input.StructureFieldCells

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

def outputFields (pointer : BitVec 64) (words counts : Nat → BitVec 64) : List StructureStore.Field := [
  (0,.op .add [localVar "p",localVar "o0"],pointer + words 0),
  (8,localVar "n0",counts 0),
  (16,.op .add [localVar "p",localVar "o1"],pointer + words 1),
  (24,localVar "n1",counts 1),
  (32,.op .add [localVar "p",localVar "o2"],pointer + words 2),
  (40,localVar "n2",counts 2),
  (48,.op .add [localVar "p",localVar "o3"],pointer + words 3),
  (56,localVar "n3",counts 3),
  (64,.op .add [localVar "p",localVar "o4"],pointer + words 4),
  (72,localVar "n4",counts 4)]

theorem output_shape (pointer : BitVec 64) (words counts : Nat → BitVec 64) : countStage 5 = StructureStore.fieldProgram "rq" (outputFields pointer words counts) := by
  simp only [countStage,countCalls,afterAllocation,afterOffsets,offsetTail,body,Guest.guestFn_decode_requests,Payload.dropLeading,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,StructureStore.fieldProgram,outputFields,Scalar.plus,localVar]

theorem output_valid (pointer : BitVec 64) (words counts : Nat → BitVec 64) :
    ∀ field ∈ outputFields pointer words counts,field.1 + 8 ≤ 80 ∧ field.1 % 8 = 0 := by
  intro field member
  simp only [outputFields,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide

/-- Ten actual original request output fields and the real request pointer
return, with exact memory and all copied bytes. -/
theorem output_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (blob pointer cursor total : BitVec 64)
    (words counts : Nat → BitVec 64) (model : CountLocals source words total pointer cursor)
    (bindings : ∀ index < 5,source.locals.lookup (ofString (countName index)) = some (.val (.word (counts index))))
    (heap : Blob.HeapInput source input blob) (domain : source.memaddrs = InitE.ordinaryDomain) (arena : Arena cursor 80)
    (blobAligned : blob.toNat % 8 = 0) (cursorAligned : cursor.toNat % 8 = 0)
    (afterInput : blob.toNat + input.length % 2^64 + 8 ≤ cursor.toNat) :
    evaluateHOLFiniteState source (countStage 5) =
      (some (.returned (.val (.word cursor))),emptyLocalsHOLFinite (Payload.applyFields source cursor (outputFields pointer words counts))) ∧
      Blob.HeapInput (Payload.applyFields source cursor (outputFields pointer words counts)) input blob := by
  have reads (current : PanSemStateFiniteExact 64 Guest.HostMemory) (locals : current.locals = source.locals) (bytes : Blob.HeapInput current input blob)
      (field : StructureStore.Field) (member : field ∈ outputFields pointer words counts) : eval current field.2.1 = some (.val (.word field.2.2)) := by
    have pointerRead (index : Nat) (small : index < 5) : eval current (.op .add [localVar "p",localVar (offsetName index)]) = some (.val (.word (pointer + words index))) := by
      have offset := model.offsets index small
      simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,locals,model.pointer,offset,valueIsWord,valueWord,wordOpHOL,wordOp]
    have countRead (index : Nat) (small : index < 5) : eval current (localVar (countName index)) = some (.val (.word (counts index))) :=
      Request.local_word current (countName index) (counts index) (by rw [locals]; exact bindings index small)
    simp only [outputFields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pointerRead 0 (by decide)
    · exact countRead 0 (by decide)
    · exact pointerRead 1 (by decide)
    · exact countRead 1 (by decide)
    · exact pointerRead 2 (by decide)
    · exact countRead 2 (by decide)
    · exact pointerRead 3 (by decide)
    · exact countRead 3 (by decide)
    · exact pointerRead 4 (by decide)
    · exact countRead 4 (by decide)
  rw [output_shape pointer words counts]
  exact StructureStore.fields_execute source input blob cursor 80 "rq" heap model.cursor domain arena blobAligned cursorAligned afterInput
    (outputFields pointer words counts) (output_valid pointer words counts) reads

/-- Exact pointer/count cells of every returned original request list. -/
theorem output_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor pointer : BitVec 64) (words counts : Nat → BitVec 64)
    (arena : Arena cursor 80) (index : Nat) (small : index < 5) :
    (Payload.applyFields source cursor (outputFields pointer words counts)).memory (cursor + BitVec.ofNat 64 (16*index)) = .word (pointer + words index) ∧
    (Payload.applyFields source cursor (outputFields pointer words counts)).memory (cursor + BitVec.ofNat 64 (16*index+8)) = .word (counts index) := by
  have valid : ∀ field ∈ outputFields pointer words counts,field.1 < 80 := by
    intro field member
    have bounds := output_valid pointer words counts field member
    omega
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · constructor
    · have cell := StructureStore.apply_fields_cell source cursor 80 arena (outputFields pointer words counts) valid 0 (by decide)
      simpa [outputFields,Payload.cellValue] using cell
    · have cell := StructureStore.apply_fields_cell source cursor 80 arena (outputFields pointer words counts) valid 8 (by decide)
      simpa [outputFields,Payload.cellValue] using cell
  · constructor
    · have cell := StructureStore.apply_fields_cell source cursor 80 arena (outputFields pointer words counts) valid 16 (by decide)
      simpa [outputFields,Payload.cellValue] using cell
    · have cell := StructureStore.apply_fields_cell source cursor 80 arena (outputFields pointer words counts) valid 24 (by decide)
      simpa [outputFields,Payload.cellValue] using cell
  · constructor
    · have cell := StructureStore.apply_fields_cell source cursor 80 arena (outputFields pointer words counts) valid 32 (by decide)
      simpa [outputFields,Payload.cellValue] using cell
    · have cell := StructureStore.apply_fields_cell source cursor 80 arena (outputFields pointer words counts) valid 40 (by decide)
      simpa [outputFields,Payload.cellValue] using cell
  · constructor
    · have cell := StructureStore.apply_fields_cell source cursor 80 arena (outputFields pointer words counts) valid 48 (by decide)
      simpa [outputFields,Payload.cellValue] using cell
    · have cell := StructureStore.apply_fields_cell source cursor 80 arena (outputFields pointer words counts) valid 56 (by decide)
      simpa [outputFields,Payload.cellValue] using cell
  · constructor
    · have cell := StructureStore.apply_fields_cell source cursor 80 arena (outputFields pointer words counts) valid 64 (by decide)
      simpa [outputFields,Payload.cellValue] using cell
    · have cell := StructureStore.apply_fields_cell source cursor 80 arena (outputFields pointer words counts) valid 72 (by decide)
      simpa [outputFields,Payload.cellValue] using cell

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.output_shape
#print axioms InitECandidate.Solver.Input.Requests.output_valid
#print axioms InitECandidate.Solver.Input.Requests.output_execute

#print axioms InitECandidate.Solver.Input.Requests.output_cells
