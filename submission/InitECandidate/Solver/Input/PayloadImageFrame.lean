import InitECandidate.Solver.Input.PayloadImage

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- Only the seventeen physical payload cells are required to retain its image. -/
theorem Image.of_cells (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length array : BitVec 64) (image : Image source input pointer cursor length array)
    (frame : ∀ field∈imageFields input pointer length array,target.memory (cursor+BitVec.ofNat 64 field.1)=source.memory (cursor+BitVec.ofNat 64 field.1)) :
    Image target input pointer cursor length array := by
  intro field member
  exact (frame field member).trans (image field member)

/-- Full payload-image retention from agreement on its actual136-byte region. -/
theorem Image.of_region (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length array : BitVec 64) (room : cursor.toNat+136≤33806089496)
    (image : Image source input pointer cursor length array)
    (frame : ∀ query,cursor.toNat≤query.toNat → query.toNat<cursor.toNat+136 → target.memory query=source.memory query) :
    Image target input pointer cursor length array := by
  apply Image.of_cells source target input pointer cursor length array image
  intro field member
  have bound := (image_fields_valid input pointer length array field member).1
  have number : (cursor+BitVec.ofNat 64 field.1).toNat=cursor.toNat+field.1 := byteAddress_toNat cursor field.1 (by omega)
  exact frame _ (by rw [number]; omega) (by rw [number]; omega)

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.Image.of_cells
#print axioms InitECandidate.Solver.Input.Payload.Image.of_region
