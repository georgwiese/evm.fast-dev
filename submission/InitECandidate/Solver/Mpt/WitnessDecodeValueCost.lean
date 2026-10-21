import InitECandidate.Solver.Mpt.WitnessDecodeRows
import InitECandidate.Solver.Mpt.WitnessDecodeAllocationCost
import InitECandidate.Solver.Mpt.WitnessDecodeControl
import InitECandidate.Solver.Rlp.ItemCallFrame

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem after_value_price (code) (installed : Input.OriginalCode.Installed code) :
    Input.ClockCost.Bound code afterValue 3 := by
  intro source codeEq
  have currentInstalled : Input.OriginalCode.Installed source.code:=by rw [codeEq]; exact installed
  have price:=Fail.guard_reached_cost source (.cmp .notEqual (field "vi" 0) (.const 0#64)) 6#64 leafAllocate 3 currentInstalled
    (fun _=>leaf_allocation_price code installed source codeEq)
  rw [after_value_shape]
  exact price.trans (by decide)

/-- The original leaf's value item is read from its current actual row;
all parser failures and the real leaf constructor/metadata tail are covered. -/
theorem value_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer cursor limit : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (selected : items[1]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source leafBody).2.clock≤60*bytes+45 := by
  obtain ⟨args,positive,small,lower,upper⟩:=rows.arguments source array pointer bytes 1 items item selected arrayCell
  have fits : (Rlp.Slices.itemPointer pointer items 1).toNat+item.total.toNat<2^64:=upper.trans_lt rows.fits
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_item") Rlp.Item.body Rlp.Item.resultShape
    (Rlp.Slices.itemPointer pointer items 1) item.total (Rlp.Item.original_code source.code installed)
  have entryArena:=Rlp.Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  have price:=Rlp.Item.body_cost (callEntryStateHOLFinite source callee) _ item.total cursor limit pointerLocal lengthLocal entryArena fits installed
  rw [value_shape]
  have full:=Input.ClockCost.scoped_current source (ofString "vi") Rlp.Item.resultShape (ofString "rlp_item") (recordArguments 1) _ Rlp.Item.body afterValue callee Rlp.Item.resultShape
    (60*item.total.toNat+41) 3 args called price (after_value_price source.code installed)
  exact full.trans (by omega)

/-- The actual leaf continuation always exits before the extension path.
Only the selected original branch's item/record allowance is charged. -/
theorem after_compact_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer cursor limit nibbles nibbleLength leaf : BitVec 64) (bytes : Nat)
    (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (selected : items[1]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (compactCell : source.locals.lookup (ofString "cn")=some (.rStruct [.val (.word nibbles),.val (.word nibbleLength),.val (.word leaf)]))
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterCompact).2.clock≤60*bytes+45 := by
  rw [compact_choice source nibbles nibbleLength leaf compactCell]
  split
  · exact value_cost source array pointer cursor limit bytes items item rows selected arrayCell arena installed
  · exact (extension_price source.code installed source rfl).trans (by omega)

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.after_value_price
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.value_cost
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.after_compact_cost
