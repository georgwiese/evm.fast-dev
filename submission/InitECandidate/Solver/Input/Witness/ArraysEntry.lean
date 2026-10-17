import InitECandidate.Solver.Input.Witness.OffsetValues
import InitECandidate.Solver.Input.Witness.LoadedOffsets

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Reach the actual node-list call from normal execution of the genuine
three-offset loop/validator/loads. Validated slice geometry, loaded locals,
unchanged fixed metadata and preserved nonscratch memory are conclusions. -/
theorem arrays_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array total : BitVec 64) (start : Nat)
    (heap : Blob.HeapInput source input pointer) (extent : start+12≤input.length%2^64)
    (wp : source.locals.lookup (ofString "wp")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (wlen : source.locals.lookup (ofString "wlen")=some (.val (.word total)))
    (offsets : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (pointerAligned : pointer.toNat%8=0)
    (arrayAligned : array.toNat%8=0) (arrayLower : 2701131776≤array.toNat)
    (before : array.toNat+24≤pointer.toNat) (upper : pointer.toNat+input.length%2^64+8≤33806089496)
    (code : source.code.lookup (ofString "ssz_check_offsets")=some (Offsets.formals,Offsets.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (enough : 8≤source.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source offsetBody=(some (.returned value),post)) :
    offsetNat input start 0=12 ∧ 12≤offsetNat input start 1 ∧
      offsetNat input start 1≤offsetNat input start 2 ∧ offsetNat input start 2≤total.toNat ∧
      ∃ loadedSource innerPost paid,
        let ready:=loadedState loadedSource input start
        paid≤8 ∧ ready.clock=source.clock-paid ∧ BackingLayout.control ready=BackingLayout.control source ∧
          Blob.HeapInput ready input pointer ∧
          (∀ name,name≠ofString "i" ∧ name≠ofString "w0" ∧ name≠ofString "w1" ∧ name≠ofString "w2" →
            ready.locals.lookup name=source.locals.lookup name) ∧
          ready.locals.lookup (ofString "w0")=some (.val (.word (offsetWord input start 0))) ∧
          ready.locals.lookup (ofString "w1")=some (.val (.word (offsetWord input start 1))) ∧
          ready.locals.lookup (ofString "w2")=some (.val (.word (offsetWord input start 2))) ∧
          (∀ query,query.toNat<array.toNat ∨ array.toNat+24≤query.toNat → ready.memory query=source.memory query) ∧
          evaluateHOLFiniteState ready nodeCall=(some (.returned value),innerPost) ∧
          post=restore source "i" (restoreLoaded loadedSource input start innerPost) := by
  classical
  obtain ⟨first,valid,loadedSource,oldInner,paid,bound,clock,control,loadedHeap,other,cells,loadedRun,postEq,frame⟩:=
    offsets_normal source post input pointer array total start heap extent wp wlen offsets domain pointerAligned arrayAligned arrayLower before upper
      code failCode exceptionShape enough value run
  have values:=offset_values input start total first valid
  have domains : loadedSource.memaddrs=source.memaddrs:=congrArg (fun state=>state.memaddrs) control
  have globals : loadedSource.globals=source.globals:=congrArg (fun state=>state.globals) control
  have loadedOffsets : loadedSource.globals.lookup (ofString "ssz_offs")=some (.val (.word array)) := by rw [globals];exact offsets
  have mapped : ∀ position<3,loadedSource.memaddrs (byteAddress array (8*position)) := by
    intro position inside
    exact word_mapped loadedSource array 24 (8*position) (domains.trans domain) ⟨arrayLower,by omega⟩ (by omega) arrayAligned (by omega)
  have actual:=loaded_offsets_execute loadedSource input array start loadedOffsets mapped cells
  have normal:=actual.symm.trans loadedRun
  let ready:=loadedState loadedSource input start
  let innerPost:=(evaluateHOLFiniteState ready nodeCall).2
  have result:=congrArg Prod.fst normal
  have nextRun : evaluateHOLFiniteState ready nodeCall=(some (.returned value),innerPost):=Prod.ext result rfl
  have innerEq : oldInner=restoreLoaded loadedSource input start innerPost:=(congrArg Prod.snd normal).symm
  have localFacts:=loaded_offset_locals loadedSource input start
  refine ⟨values.1,values.2.1,values.2.2.1,values.2.2.2,loadedSource,innerPost,paid,bound,clock,control,loadedHeap,
    ?_,localFacts.1,localFacts.2.1,localFacts.2.2,frame,nextRun,?_⟩
  · intro name different
    exact (loaded_other_local loadedSource input start name different.2).trans (other name different.1)
  · rw [postEq,innerEq]

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.arrays_entry
