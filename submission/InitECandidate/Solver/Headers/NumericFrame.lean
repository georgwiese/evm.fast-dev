import InitECandidate.Solver.Headers.UintScopeFrame
import InitECandidate.Solver.Headers.WordCost
import InitECandidate.Solver.Headers.U256Cost
import InitECandidate.Solver.Input.LocalEffectsLoop

namespace InitECandidate.Solver.Headers.WordField
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- All original word-field tail outcomes modify only locals and clock. -/
theorem after_field_readonly (code) : Input.LocalEffects.Preserves code afterField := by
  rw [field_shape,after_guard_shape,loop_shape]
  unfold loopBody accumulate increment
  repeat first
    | apply Input.LocalEffects.sequence
    | apply Input.LocalEffects.conditional
    | apply Input.LocalEffects.declared
    | apply Input.LocalEffects.loop
    | exact Input.LocalEffects.assign code _ _
    | exact Input.LocalEffects.raised code _ _
    | exact Input.LocalEffects.returned code _
    | exact Input.LocalEffects.skip code

end InitECandidate.Solver.Headers.WordField

namespace InitECandidate.Solver.Headers.U256Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- The real four-word field tail uses only the already checked read-only
u256_from_be and local guard/return operations. -/
theorem after_field_readonly (code) (installed : Input.OriginalCode.Installed code) : Input.LocalEffects.Preserves code afterField := by
  rw [field_shape,after_guard_shape]
  apply Input.LocalEffects.sequence
  · exact Input.LocalEffects.conditional code _ _ _ (Input.LocalEffects.raised code _ _) (Input.LocalEffects.skip code)
  · exact Input.LocalEffects.scoped_body code _ _ (ofString "u256_from_be") _ _ [(ofString "p",.one),(ofString "n",.one)]
      GasBudget.U256FromBe.body Input.RlpWrite.U256Value.tupleShape (GasBudget.U256FromBe.original_code code installed)
      (GasBudget.ArithmeticEffects.pure_u256_from_be code (GasBudget.OriginalCodeEnvironment.arithmetic code installed))
      (Input.LocalEffects.returned code _)

end InitECandidate.Solver.Headers.U256Field

namespace InitECandidate.Solver.Headers
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Whole original numerical header-field normal frames, with actual row
provenance and no supplied future numeric value or successful suffix. -/
theorem word_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer cursor limit : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (selected : items[index]?=some item) (model : Rlp.ListItems source pointer bytes items)
    (records : Rlp.Slices.Records source.memory array pointer items)
    (arena : Rlp.Validation.Arena source cursor limit) (allocation : AllocatedBytes.Arena array (16*items.length))
    (arrayAligned : array.toNat%8=0) (fits : pointer.toNat+bytes<2^64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source WordField.body=(some (.returned value),post)) :
    Rlp.Validation.Arena post cursor limit ∧ Rlp.Validation.Above source post cursor.toNat ∧
      (∀ key,post.globals.lookup key=source.globals.lookup key) := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) WordField.arguments=some (Field.Kind.uint.values array (BitVec.ofNat 64 index) 0#64) := by
    simp [WordField.arguments,Field.Kind.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,arrayCell,indexCell]
  rw [WordField.body_shape] at normal
  exact Field.uint_scope_normal_frame source post array pointer cursor limit 0#64 bytes index items item selected model records arena allocation arrayAligned fits
    "f" WordField.arguments WordField.afterField args installed (WordField.after_field_readonly source.code) value normal

theorem u256_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer cursor limit maximum : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (selected : items[index]?=some item) (model : Rlp.ListItems source pointer bytes items)
    (records : Rlp.Slices.Records source.memory array pointer items)
    (arena : Rlp.Validation.Arena source cursor limit) (allocation : AllocatedBytes.Arena array (16*items.length))
    (arrayAligned : array.toNat%8=0) (fits : pointer.toNat+bytes<2^64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (maximumCell : source.locals.lookup (ofString "maxb")=some (.val (.word maximum)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source U256Field.body=(some (.returned value),post)) :
    Rlp.Validation.Arena post cursor limit ∧ Rlp.Validation.Above source post cursor.toNat ∧
      (∀ key,post.globals.lookup key=source.globals.lookup key) := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) U256Field.arguments=some (Field.Kind.uint.values array (BitVec.ofNat 64 index) maximum) := by
    simp [U256Field.arguments,Field.Kind.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,arrayCell,indexCell,maximumCell]
  rw [U256Field.body_shape] at normal
  exact Field.uint_scope_normal_frame source post array pointer cursor limit maximum bytes index items item selected model records arena allocation arrayAligned fits
    "f" U256Field.arguments U256Field.afterField args installed (U256Field.after_field_readonly source.code installed) value normal

end InitECandidate.Solver.Headers

#print axioms InitECandidate.Solver.Headers.WordField.after_field_readonly
#print axioms InitECandidate.Solver.Headers.U256Field.after_field_readonly
#print axioms InitECandidate.Solver.Headers.word_normal_frame
#print axioms InitECandidate.Solver.Headers.u256_normal_frame
