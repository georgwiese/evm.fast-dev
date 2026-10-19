import InitECandidate.Solver.Mpt.AccountFieldView
import InitECandidate.Solver.Rlp.ItemCallEncoding

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
attribute [local instance] Classical.propDecidable

/-- A normal field call derives its real tuple, physical/input view, memory
frame and genuine continuation. Unmapped record cases contradict the actual
normal result; no mapping or successful future helper is assumed. -/
theorem field_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer length cursor limit out : BitVec 64) (cutoff : Nat) (items : List Rlp.ListItem)
    (index : Nat) (item : Rlp.ListItem) (name : String) (continuation : ProgHOL 64)
    (view : FieldsView source array pointer length cursor limit out cutoff items) (selected : items[index]?=some item)
    (arrayOther : ofString name≠ofString "arr") (outputOther : ofString name≠ofString "acct_out")
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) Rlp.Item.resultShape (ofString "rlp_item") (fieldArguments index) continuation)=
      (some (.returned returned),post)) :
    ∃ calleePost header payload flag inner,
      Rlp.Item.Valid (Rlp.Slices.itemPointer pointer items index) item.total.toNat
        (Rlp.Item.result (Rlp.Slices.itemPointer pointer items index) header payload flag) ∧
      (header=item.header ∧ payload=item.payload ∧ flag=item.flag) ∧
      FieldsView (Input.CallNormal.continuationEntry source calleePost name (Rlp.Item.result (Rlp.Slices.itemPointer pointer items index) header payload flag))
        array pointer length cursor limit out cutoff items ∧
      Rlp.Validation.Above source calleePost cursor.toNat ∧ calleePost.memaddrs=source.memaddrs ∧ calleePost.be=source.be ∧ calleePost.code=source.code ∧
      calleePost.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") ∧
      source.clock-calleePost.clock≤60*item.size+42 ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source calleePost name (Rlp.Item.result (Rlp.Slices.itemPointer pointer items index) header payload flag))
        continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  have args := field_arguments_cases source array pointer items index item view.arrayCell view.records selected
  obtain ⟨number,positive,bounded,fits⟩ := Rlp.ListItems.at_span source pointer length.toNat items view.itemsModel index item selected view.inputFits
  obtain ⟨offset,path,inside,itemValid,itemEncoding⟩ := Rlp.ListItems.at source pointer length.toNat items view.itemsModel index item selected
  have prior : Rlp.Header.Encoded source (Rlp.Slices.itemPointer pointer items index) item.header item.payload item.flag := by
    rw [path]
    exact itemEncoding
  by_cases firstMapped : source.memaddrs (array+BitVec.ofNat 64 (16*index))
  · by_cases secondMapped : source.memaddrs (array+BitVec.ofNat 64 (16*index)+8#64)
    · rw [if_pos firstMapped,if_pos secondMapped] at args
      obtain ⟨positive,calleePost,header,payload,flag,inner,valid,encoded,nextArena,above,domain,endian,codeEq,heapEq,price,tailRun,restored⟩ :=
        Rlp.Item.scoped_normal_encoded source post (Rlp.Slices.itemPointer pointer items index) item.total cursor limit name (fieldArguments index) continuation
          args view.arena fits installed returned normal
      have nextView := FieldsView.resumed source calleePost array pointer length cursor limit out cutoff items name
        (Rlp.Item.result (Rlp.Slices.itemPointer pointer items index) header payload flag) view arrayOther outputOther nextArena above domain endian
      rw [number] at price
      have matching := Rlp.Header.Encoded.unique source (Rlp.Slices.itemPointer pointer items index) header payload flag item.header item.payload item.flag encoded prior
      exact ⟨calleePost,header,payload,flag,inner,valid,matching,nextView,above,domain,endian,codeEq,heapEq,price,tailRun,restored⟩
    · rw [if_pos firstMapped,if_neg secondMapped] at args
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at normal
      simp only [args] at normal
      cases normal
  · rw [if_neg firstMapped] at args
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at normal
    simp only [args] at normal
    cases normal

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.field_normal
