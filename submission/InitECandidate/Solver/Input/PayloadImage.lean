import InitECandidate.Solver.Input.PayloadAfterExtraNormal
import InitECandidate.Solver.Input.PayloadMemoryFields

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Values of the actual fifteen writes after the initial payload header.
The expressions are the unchanged original store expressions; this list is
physical-image metadata, with the real transaction call's returned tuple. -/
def afterExtraFields (input : Guest.InputBlob) (pointer length array : BitVec 64) : List Field :=
  [(16,extraPointerValue,pointer+602#64),
   (24,extraLength,BitVec.ofNat 64 (Guest.GasLimit.le32 input 566-540)),
   (32,.rfield 0 (localVar "txs"),VarList.decodedArray array (transactionBytes input)),
   (40,.rfield 1 (localVar "txs"),BitVec.ofNat 64 (transactionCount input))] ++
  remainingFields input pointer length (offsetWords input 2) (offsetWords input 3) (BitVec.ofNat 64 (withdrawalCount input))

def imageFields (input : Guest.InputBlob) (pointer length array : BitVec 64) : List Field :=
  [(0,localVar "p",pointer+62#64),(8,localVar "len",length)] ++ afterExtraFields input pointer length array

/-- Every actual payload word, including the transaction-array pointer/count. -/
def Image (post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer cursor length array : BitVec 64) : Prop :=
  ∀ field∈imageFields input pointer length array,post.memory (cursor+BitVec.ofNat 64 field.1)=.word field.2.2

theorem image_fields_valid (input : Guest.InputBlob) (pointer length array : BitVec 64) :
    ∀ field∈imageFields input pointer length array,field.1≤128 ∧ field.1%8=0 := by
  intro field member
  simp only [imageFields,afterExtraFields,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with (rfl | rfl) | (rfl | rfl | rfl | rfl) | member
  all_goals first | exact remaining_valid input pointer length (offsetWords input 2) (offsetWords input 3) (BitVec.ofNat 64 (withdrawalCount input)) field member | (simp only [Prod.fst]; decide)

theorem Image.of_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length array : BitVec 64) (memory : target.memory=source.memory) (image : Image source input pointer cursor length array) : Image target input pointer cursor length array := by
  intro field member
  rw [memory]
  exact image field member

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.image_fields_valid
#print axioms InitECandidate.Solver.Input.Payload.Image.of_memory
