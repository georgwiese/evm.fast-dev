import InitECandidate.Solver.Mpt.AccountAfterSlicesCost
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual normal count guarding derives four physical records and reaches
the genuine field-call fragment. The guard's expected count is a conclusion. -/
theorem after_slices_fields (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer length cursor limit out count : BitVec 64) (cutoff : Nat) (items : List Rlp.ListItem)
    (sliceCell : source.locals.lookup (ofString "sl")=some (Rlp.Slices.result array count))
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (arena : Rlp.Validation.Arena source cursor limit) (model : Rlp.ListItems source pointer length.toNat items)
    (records : Rlp.Slices.Records source.memory array pointer items) (countEq : count.toNat=items.length)
    (inputFits : pointer.toNat+length.toNat<2^64) (before : pointer.toNat+length.toNat≤array.toNat)
    (room : array.toNat+16*count.toNat≤33806089496)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (output : Output out) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterSlices=(some (.returned returned),post)) :
    count=4#64 ∧ items.length=4 ∧ ∃ inner,
      FieldsView (bind source "arr" array) array pointer length cursor limit out cutoff items ∧
      evaluateHOLFiniteState (bind source "arr" array) fields=(some (.returned returned),inner) ∧
      post=restore source "arr" inner := by
  have shape : afterSlices=.seq (.ite (.cmp .notEqual (field "sl" 1) (.const 4#64)) (fail 20#64) .skip)
      (.dec (ofString "arr") .one (field "sl" 0) fields) := by rw [after_slices_shape,fields_shape]
  rw [shape] at normal
  have safe : Input.LocalPrefix (ofString "acct_out") (.ite (.cmp .notEqual (field "sl" 1) (.const 4#64)) (fail 20#64) .skip) :=
    .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨middle,guardRun,tailRun,outputEq⟩ := safe.normal_continue source post (.dec (ofString "arr") .one (field "sl" 0) fields) returned normal
  obtain ⟨passed,middleEq⟩ := Fail.guard_normal source middle _ [.const 20#64] installed guardRun
  subst middle
  have countRead : eval source (field "sl" 1)=some (.val (.word count)) := by
    simp [field,eval,evalHOLExact,localVar,toExact,sliceCell,Rlp.Slices.result]
  have countFour := Input.CompareFacts.not_equal_zero source (field "sl" 1) (.const 4#64) count 4#64 countRead rfl passed
  have lengthFour : items.length=4 := by rw [←countEq,countFour]; rfl
  have arrayRead : eval source (field "sl" 0)=some (.val (.word array)) := by
    simp [field,eval,evalHOLExact,localVar,toExact,sliceCell,Rlp.Slices.result]
  obtain ⟨inner,fieldsRun,restored⟩ := Input.declaration_return_word source post "arr" (field "sl" 0) array fields returned arrayRead tailRun
  let ready := bind source "arr" array
  have readyModel := Rlp.ListItems.transport source ready pointer length.toNat items model length.isLt (by intro offset inside; rfl)
  have view : FieldsView ready array pointer length cursor limit out cutoff items :=
    ⟨Rlp.Validation.Arena.of_fields source ready cursor limit arena rfl rfl,bind_lookup_same _ _ _,
      (bind_lookup_other _ "arr" "acct_out" _ (by decide)).trans outputCell,
      readyModel,records,inputFits,before,by rw [←countEq]; omega,aligned,scratchBelow,inputAbove,output⟩
  exact ⟨countFour,lengthFour,inner,view,fieldsRun,restored⟩

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_slices_fields
