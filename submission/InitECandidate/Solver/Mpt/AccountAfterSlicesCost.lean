import InitECandidate.Solver.Mpt.AccountFieldsCost
import InitECandidate.Solver.Rlp.SlicesCallNormal
import InitECandidate.Solver.Input.CompareZero

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real four-item guard either stops or derives exactly the four
records used by the original field calls. No expected count is assumed. -/
theorem after_slices_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer length cursor limit out count : BitVec 64) (cutoff : Nat) (items : List Rlp.ListItem)
    (sliceCell : source.locals.lookup (ofString "sl")=some (Rlp.Slices.result array count))
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (arena : Rlp.Validation.Arena source cursor limit) (model : Rlp.ListItems source pointer length.toNat items)
    (records : Rlp.Slices.Records source.memory array pointer items) (countEq : count.toNat=items.length)
    (inputFits : pointer.toNat+length.toNat<2^64) (before : pointer.toNat+length.toNat≤array.toNat)
    (room : array.toNat+16*count.toNat≤33806089496)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (output : Output out) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterSlices).2.clock≤60*length.toNat+212 := by
  have shape : afterSlices=.seq (.ite (.cmp .notEqual (field "sl" 1) (.const 4#64)) (fail 20#64) .skip)
      (.dec (ofString "arr") .one (field "sl" 0) fields) := by
    rw [after_slices_shape,fields_shape]
  rw [shape]
  have priced := Fail.guard_reached_cost source (.cmp .notEqual (field "sl" 1) (.const 4#64)) 20#64
    (.dec (ofString "arr") .one (field "sl" 0) fields) (60*length.toNat+212) installed ?_
  · simpa only [fail] using priced.trans (by omega)
  · intro passed
    have countRead : eval source (field "sl" 1)=some (.val (.word count)) := by
      simp [field,eval,evalHOLExact,localVar,toExact,sliceCell,Rlp.Slices.result]
    have test := (Fail.guard_normal source source _ [.const 20#64] installed passed).1
    have countFour := Input.CompareFacts.not_equal_zero source (field "sl" 1) (.const 4#64) count 4#64 countRead rfl test
    have lengthFour : items.length=4 := by rw [←countEq,countFour]; rfl
    obtain ⟨a,b,c,d,itemsEq⟩ := List.length_eq_four.mp lengthFour
    subst items
    have arrayRead : eval source (field "sl" 0)=some (.val (.word array)) := by
      simp [field,eval,evalHOLExact,localVar,toExact,sliceCell,Rlp.Slices.result]
    let ready := bind source "arr" array
    have readyModel := Rlp.ListItems.transport source ready pointer length.toNat [a,b,c,d] model length.isLt (by intro offset inside; rfl)
    have view : FieldsView ready array pointer length cursor limit out cutoff [a,b,c,d] :=
      ⟨Rlp.Validation.Arena.of_fields source ready cursor limit arena rfl rfl,bind_lookup_same _ _ _,
        (bind_lookup_other _ "arr" "acct_out" _ (by decide)).trans outputCell,
        readyModel,records,inputFits,before,by rw [←countEq]; omega,aligned,scratchBelow,inputAbove,output⟩
    exact Input.ClockCost.declared_current source "arr" (field "sl" 0) array fields (60*length.toNat+212) arrayRead
      (fields_cost ready array pointer length cursor limit out cutoff a b c d view installed)

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_slices_cost
