import InitECandidate.Solver.Mpt.AccountFieldView

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
attribute [local instance] Classical.propDecidable

/-- Price a real field call from the actual array record and input span.
Failed record mapping checks stop before the callee clock; genuine returns
derive the next physical/input view before pricing their continuation. -/
theorem field_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer length cursor limit out : BitVec 64) (cutoff : Nat) (items : List Rlp.ListItem)
    (index : Nat) (item : Rlp.ListItem) (name : String) (continuation : ProgHOL 64) (tailPrice : Nat)
    (view : FieldsView source array pointer length cursor limit out cutoff items) (selected : items[index]?=some item)
    (arrayOther : ofString name≠ofString "arr") (outputOther : ofString name≠ofString "acct_out")
    (installed : Input.OriginalCode.Installed source.code)
    (tail : ∀ post header payload flag,
      Rlp.Item.Valid (Rlp.Slices.itemPointer pointer items index) item.total.toNat
        (Rlp.Item.result (Rlp.Slices.itemPointer pointer items index) header payload flag) →
      FieldsView (Input.CallNormal.continuationEntry source post name
        (Rlp.Item.result (Rlp.Slices.itemPointer pointer items index) header payload flag)) array pointer length cursor limit out cutoff items →
      post.code=source.code →
      let ready:=Input.CallNormal.continuationEntry source post name
        (Rlp.Item.result (Rlp.Slices.itemPointer pointer items index) header payload flag)
      ready.clock-(evaluateHOLFiniteState ready continuation).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) Rlp.Item.resultShape (ofString "rlp_item") (fieldArguments index) continuation)).2.clock≤
      60*item.size+42+tailPrice := by
  have args := field_arguments_cases source array pointer items index item view.arrayCell view.records selected
  obtain ⟨number,positive,bounded,fits⟩ := Rlp.ListItems.at_span source pointer length.toNat items view.itemsModel index item selected view.inputFits
  by_cases firstMapped : source.memaddrs (array+BitVec.ofNat 64 (16*index))
  · by_cases secondMapped : source.memaddrs (array+BitVec.ofNat 64 (16*index)+8#64)
    · rw [if_pos firstMapped,if_pos secondMapped] at args
      have priced := Rlp.Item.scoped_frame_cost source (Rlp.Slices.itemPointer pointer items index) item.total cursor limit name (fieldArguments index) continuation tailPrice
        args view.arena fits installed ?_
      · rwa [number] at priced
      · intro post header payload flag valid nextArena above domain endian codeEq heapEq
        have nextView := FieldsView.resumed source post array pointer length cursor limit out cutoff items name
          (Rlp.Item.result (Rlp.Slices.itemPointer pointer items index) header payload flag) view arrayOther outputOther nextArena above domain endian
        exact tail post header payload flag valid nextView codeEq
    · rw [if_pos firstMapped,if_neg secondMapped] at args
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
      simp only [args]
      change source.clock-source.clock≤_
      omega
  · rw [if_neg firstMapped] at args
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    simp only [args]
    change source.clock-source.clock≤_
    omega

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.field_cost
