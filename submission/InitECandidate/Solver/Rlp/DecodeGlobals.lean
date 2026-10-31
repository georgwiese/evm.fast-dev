import InitECandidate.Solver.Rlp.DecodeCost
import InitECandidate.Solver.Rlp.ValidationGlobals

namespace InitECandidate.Solver.Rlp.ItemTotal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "scratch_ptr") :
    Input.GlobalEffects.Preserves key code body := by
  rw [body_shape]
  apply Input.GlobalEffects.scoped_body key code (ofString "h") Header.resultShape (ofString "rlp_item_header") _ _ Header.formals Header.body Header.resultShape
    (Header.original_code code installed) (Input.GlobalEffects.of_readonly key code Header.body (Header.readonly code installed))
  unfold afterHeader check validate
  apply Input.GlobalEffects.sequence
  · apply Input.GlobalEffects.conditional
    · exact Input.GlobalEffects.call_body key code (some none) (ofString "rlp_validate_items") _ Header.formals Validate.body .one
        (Validate.original_code code installed) (Validate.globals key code installed other)
    · exact Input.GlobalEffects.skip key code
  · exact Input.GlobalEffects.returned key code _

end InitECandidate.Solver.Rlp.ItemTotal

namespace InitECandidate.Solver.Rlp.ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "scratch_ptr") :
    Input.GlobalEffects.Preserves key code body := by
  rw [body_shape,loop_shape]
  simp only [loopBody,advance]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.loop
    | exact Input.GlobalEffects.assign key code _ _
    | exact Input.GlobalEffects.returned key code _
    | apply Input.GlobalEffects.scoped_body key code (ofString "total") .one (ofString "rlp_item_total") _ _ Header.formals ItemTotal.body .one
        (ItemTotal.original_code code installed) (ItemTotal.globals key code installed other)

end InitECandidate.Solver.Rlp.ListCount

namespace InitECandidate.Solver.Rlp.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "scratch_ptr") :
    Input.GlobalEffects.Preserves key code body := by
  simp only [body,Guest.Software.guestFn_rlp_item,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.skip key code
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "rlp_fail") _ Fail.formals Fail.body .one
        (Fail.original_code code installed) (Input.GlobalEffects.of_readonly key code Fail.body (Fail.readonly code))
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "rlp_list_count") _ Header.formals ListCount.body .one
        (ListCount.original_code code installed) (ListCount.globals key code installed other)
    | apply Input.GlobalEffects.scoped_body key code (ofString "n") .one (ofString "rlp_read_length") _ _ ReadLength.formals ReadLength.body .one
        (ReadLength.original_code code installed) (Input.GlobalEffects.of_readonly key code ReadLength.body (ReadLength.readonly code installed))

end InitECandidate.Solver.Rlp.Item

namespace InitECandidate.Solver.Rlp.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Full original RLP decoding preserves every global except scratch_ptr
on all outcomes. In particular, its scratch work leaves heap_ptr unchanged. -/
theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "scratch_ptr") :
    Input.GlobalEffects.Preserves key code body := by
  rw [body_shape]
  apply Input.GlobalEffects.scoped_body key code (ofString "it") Item.resultShape (ofString "rlp_item") _ _ Header.formals Item.body Item.resultShape
    (Item.original_code code installed) (Item.globals key code installed other)
  unfold afterItem
  exact Input.GlobalEffects.sequence key code _ _
    (Input.GlobalEffects.conditional key code _ _ _
      (Input.GlobalEffects.call_body key code (some none) (ofString "rlp_fail") _ Fail.formals Fail.body .one
        (Fail.original_code code installed) (Input.GlobalEffects.of_readonly key code Fail.body (Fail.readonly code)))
      (Input.GlobalEffects.skip key code)) (Input.GlobalEffects.returned key code _)

end InitECandidate.Solver.Rlp.Decode

#print axioms InitECandidate.Solver.Rlp.ItemTotal.globals
#print axioms InitECandidate.Solver.Rlp.ListCount.globals
#print axioms InitECandidate.Solver.Rlp.Item.globals
#print axioms InitECandidate.Solver.Rlp.Decode.globals
