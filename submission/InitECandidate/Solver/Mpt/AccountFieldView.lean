import InitECandidate.Solver.Mpt.AccountFieldArguments
import InitECandidate.Solver.Mpt.AccountDecodeOutput
import InitECandidate.Solver.Rlp.ItemCallFrame
import InitECandidate.Solver.Rlp.ByteAgreementFrame
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Current input encodings, actual physical records and arena/output
geometry at an original account field call. No future helper model occurs. -/
structure FieldsView (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer length cursor limit out : BitVec 64) (cutoff : Nat) (items : List Rlp.ListItem) : Prop where
  arena : Rlp.Validation.Arena source cursor limit
  arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array))
  outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out))
  itemsModel : Rlp.ListItems source pointer length.toNat items
  records : Rlp.Slices.Records source.memory array pointer items
  inputFits : pointer.toNat+length.toNat<2^64
  inputBefore : pointer.toNat+length.toNat≤array.toNat
  arrayFits : array.toNat+16*items.length<2^64
  aligned : cutoff%8=0
  scratchBelow : cursor.toNat≤cutoff
  inputAbove : cutoff≤pointer.toNat
  output : Output out

/-- Actual RLP scratch preservation carries both the input encodings and
the already built array into the resumed caller. Only its real result's
binding is replaced, with the original array/output locals restored. -/
theorem FieldsView.resumed (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer length cursor limit out : BitVec 64) (cutoff : Nat) (items : List Rlp.ListItem)
    (name : String) (value : ValueHOL 64) (view : FieldsView source array pointer length cursor limit out cutoff items)
    (arrayOther : ofString name≠ofString "arr") (outputOther : ofString name≠ofString "acct_out")
    (arena : Rlp.Validation.Arena post cursor limit) (above : Rlp.Validation.Above source post cursor.toNat)
    (domain : post.memaddrs=source.memaddrs) (endian : post.be=source.be) :
    FieldsView (Input.CallNormal.continuationEntry source post name value) array pointer length cursor limit out cutoff items := by
  let ready := Input.CallNormal.continuationEntry source post name value
  have readyArena := Rlp.Validation.Arena.of_fields post ready cursor limit arena rfl rfl
  have byteFrame := Rlp.Validation.Above.bytes_agree source post cutoff pointer length
    (Rlp.Validation.Above.mono source post cursor.toNat cutoff above view.scratchBelow) view.aligned view.inputAbove view.inputFits domain endian
  have postItems := Rlp.ListItems.transport source post pointer length.toNat items view.itemsModel length.isLt byteFrame
  have readyItems := Rlp.ListItems.transport post ready pointer length.toNat items postItems length.isLt (by intro offset inside; rfl)
  have readyRecords := Rlp.Slices.Records.above source post array pointer items cursor.toNat view.records above
    (by have := view.scratchBelow; have := view.inputAbove; have := view.inputBefore; omega) view.arrayFits
  exact ⟨readyArena,
    (Input.CallNormal.continuation_lookup_other source post name "arr" value arrayOther).trans view.arrayCell,
    (Input.CallNormal.continuation_lookup_other source post name "acct_out" value outputOther).trans view.outputCell,
    readyItems,readyRecords,view.inputFits,view.inputBefore,view.arrayFits,view.aligned,view.scratchBelow,view.inputAbove,view.output⟩

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.FieldsView.resumed
