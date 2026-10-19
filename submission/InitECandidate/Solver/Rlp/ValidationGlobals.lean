import InitECandidate.Solver.Rlp.ValidationWrapper
import InitECandidate.Solver.Arenas.GlobalEffects
import InitECandidate.Solver.Input.GlobalEffectsCaught

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original internal validation may write its scratch records and cursor,
but preserves every other selected global on all outcomes. -/
theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "scratch_ptr") :
    Input.GlobalEffects.Preserves key code body := by
  rw [body_shape,loop_shape,loop_body_shape]
  simp only [atEnd,stop,pop,parse,afterHeader,choose,push,pushStores,pushMoves,move]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | apply Input.GlobalEffects.loop
    | exact Input.GlobalEffects.assign key code _ _
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.returned key code _
    | apply Input.GlobalEffects.scoped_body key code (ofString "h") Header.resultShape (ofString "rlp_item_header") _ _ Header.formals Header.body Header.resultShape
        (Header.original_code code installed) (Input.GlobalEffects.of_readonly key code Header.body (Header.readonly code installed))
    | apply Input.GlobalEffects.scoped_body key code (ofString "rec") .one (ofString "scratch_alloc") _ _ Arenas.formals (Arenas.body .down) .one
        (Arenas.original_code code installed .down) (Arenas.globals key code installed .down other)

end InitECandidate.Solver.Rlp.Validation

namespace InitECandidate.Solver.Rlp.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem release_globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "scratch_ptr") :
    Input.GlobalEffects.Preserves key code release :=
  Input.GlobalEffects.call_body key code (some none) (ofString "scratch_release") _ Arenas.Scratch.formals Arenas.Scratch.releaseBody .one
    (Arenas.Scratch.release_code code installed) (Arenas.Scratch.release_globals key code other)

theorem handler_globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "scratch_ptr") :
    Input.GlobalEffects.Preserves key code handler :=
  Input.GlobalEffects.sequence key code _ _ (release_globals key code installed other) (Input.GlobalEffects.raised key code _ _)

/-- Public validation restores/reuses scratch but never changes any other
selected global, including the persistent heap cursor, on any outcome. -/
theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "scratch_ptr") :
    Input.GlobalEffects.Preserves key code body := by
  rw [body_shape]
  apply Input.GlobalEffects.scoped_body key code (ofString "mark") .one (ofString "scratch_mark") [] afterMark [] (Arenas.markBody .down) .one
    (Arenas.Scratch.mark_code code installed) (Arenas.mark_globals key code .down)
  unfold afterMark afterError
  apply Input.GlobalEffects.declared
  apply Input.GlobalEffects.sequence
  · exact Input.GlobalEffects.caught_body key code (ofString "_rlp_validate_items_body") arguments Validation.formals Validation.body .one
      (ofString "RlpErr") (ofString "e") handler (Validation.original_code code installed)
      (Validation.globals key code installed other) (handler_globals key code installed other)
  · exact Input.GlobalEffects.sequence key code _ _ (release_globals key code installed other) (Input.GlobalEffects.returned key code _)

end InitECandidate.Solver.Rlp.Validate

#print axioms InitECandidate.Solver.Rlp.Validation.globals
#print axioms InitECandidate.Solver.Rlp.Validate.release_globals
#print axioms InitECandidate.Solver.Rlp.Validate.handler_globals
#print axioms InitECandidate.Solver.Rlp.Validate.globals
