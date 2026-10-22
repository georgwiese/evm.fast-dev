import InitECandidate.Solver.Input.PayloadHeaderOmmerFrame

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main

def initialHeaderWord (slot : Nat) : BitVec 64:=if slot=1 then inputPointer+62#64 else if slot=0 then 1#64 else 0#64

theorem marked_ommer_before (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap query : BitVec 64) (layout : OmmerLayout heap) (before : query.toNat<(temporaryBase heap).toNat) :
    (markedOmmer input source heap).memory query=(parentStoredHeader input source heap).memory query := by
  have backing:=AllocatedBytes.aligned_number (temporaryBase heap)
  have aligned:=layout.temporaryAligned
  apply ByteStore.away
  intro same
  have number:=congrArg BitVec.toNat same
  omega

theorem parent_header_cells (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (layout : OmmerLayout heap) (slot : Nat) (inside : slot<31) :
    (parentStoredHeader input source heap).memory (heap+BitVec.ofNat 64 (8*slot))=.word (initialHeaderWord slot) := by
  have number:=byteAddress_toNat heap (8*slot) (by have h:=layout.headerArena.upper; omega)
  have plus8:=byteAddress_toNat heap 8 (by have h:=layout.headerArena.upper; omega)
  have same0 : (heap+BitVec.ofNat 64 (8*slot)=heap)↔slot=0:=by
    constructor
    · intro same
      have numeric:=congrArg BitVec.toNat same
      change (heap+BitVec.ofNat 64 (8*slot)).toNat=heap.toNat+8*slot at number
      omega
    · intro zero
      subst slot
      simp
  have same1 : (heap+BitVec.ofNat 64 (8*slot)=heap+8#64)↔slot=1:=by
    constructor
    · intro same
      have numeric:=congrArg BitVec.toNat same
      change (heap+BitVec.ofNat 64 (8*slot)).toNat=heap.toNat+8*slot at number
      change (heap+8#64).toNat=heap.toNat+8 at plus8
      omega
    · intro one
      subst slot
      rfl
  simp only [parentStoredHeader,markedHeader,StoreWord.put,same0,same1,cleared_cells input source heap slot inside,initialHeaderWord]
  split_ifs <;>rfl

theorem OmmerHashOutput.cells (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (layout : OmmerLayout heap) (output : OmmerHashOutput input source heap target)
    (lower : 2713717616≤heap.toNat) (slot : Nat) (inside : slot<31) :
    target.memory (heap+BitVec.ofNat 64 (8*slot))=.word (initialHeaderWord slot) := by
  have number:=byteAddress_toNat heap (8*slot) (by have h:=layout.headerArena.upper; omega)
  change (heap+BitVec.ofNat 64 (8*slot)).toNat=heap.toNat+8*slot at number
  have headerBefore:=layout.headerBefore
  have ommerBefore:=layout.ommerBefore
  rw [output.memory _ (layout.protected_before heap _ (by omega) (by omega)),
    marked_ommer_before input source heap _ layout (by omega)]
  exact parent_header_cells input source heap layout slot inside

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.marked_ommer_before
#print axioms InitECandidate.Solver.Input.PayloadHeader.parent_header_cells
#print axioms InitECandidate.Solver.Input.PayloadHeader.OmmerHashOutput.cells
