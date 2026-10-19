import InitECandidate.Solver.Rlp.SlicesGlobals
import InitECandidate.Solver.Mpt.AccountDecodeTailGlobals
import InitECandidate.Solver.Input.GlobalEffectsCaught

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

set_option maxRecDepth 10000 in
/-- Every complete original account decoder outcome preserves all globals
apart from heap/scratch cursors. This includes its real caught assignment
and MPT failure handler, list conversion, four field calls and output tail. -/
theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code)
    (notHeap : key≠ofString "heap_ptr") (notScratch : key≠ofString "scratch_ptr") :
    Input.GlobalEffects.Preserves key code body := by
  have failure (error : BitVec 64) : Input.GlobalEffects.Preserves key code (fail error) :=
    Input.GlobalEffects.call_body key code (some none) (ofString "mpt_fail") _ Fail.formals Fail.body .one
      (Fail.original_code code installed) (Input.GlobalEffects.of_readonly key code _ (Fail.readonly code))
  have caughtPure : Input.GlobalEffects.Preserves key code caught :=
    Input.GlobalEffects.caught_destination key code (some (ofString "it")) (ofString "rlp_decode_fully") decodeArguments Rlp.Header.formals Rlp.Decode.body Rlp.Item.resultShape
      (ofString "RlpErr") (ofString "e") handler (Rlp.Decode.original_code code installed) (Rlp.Decode.globals key code installed notScratch) (failure 20#64)
  rw [body_shape,after_decode_shape,after_slices_shape]
  repeat first
    | exact after_fields_globals key code installed
    | exact caughtPure
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | exact Input.GlobalEffects.skip key code
    | exact failure _
    | apply Input.GlobalEffects.scoped_body key code (ofString "sl") Rlp.Slices.resultShape (ofString "rlp_list_to_slices") _ _ Rlp.Header.formals Rlp.Slices.body Rlp.Slices.resultShape
        (Rlp.Slices.original_code code installed) (Rlp.Slices.globals key code installed notHeap notScratch)
    | apply Input.GlobalEffects.scoped_body key code _ Rlp.Item.resultShape (ofString "rlp_item") _ _ Rlp.Header.formals Rlp.Item.body Rlp.Item.resultShape
        (Rlp.Item.original_code code installed) (Rlp.Item.globals key code installed notScratch)

/-- Recover a selected incoming global at a genuinely reached tail from
actual enclosing/tail runs and their lexical restoration. No reached value
is assumed; the equalities are consequences of both real effect frames. -/
theorem reached_tail_global (source ready post inner : PanSemStateFiniteExact 64 Guest.HostMemory)
    (key : MlS) (installed : Input.OriginalCode.Installed source.code) (codeEq : ready.code=source.code)
    (notHeap : key≠ofString "heap_ptr") (notScratch : key≠ofString "scratch_ptr") (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source body=(result,post))
    (tail : evaluateHOLFiniteState ready afterFields=(result,inner))
    (frame : emptyLocalsHOLFinite post=emptyLocalsHOLFinite inner) : ready.globals.lookup key=source.globals.lookup key := by
  have whole := globals key source.code installed notHeap notScratch source rfl
  have suffix := after_fields_globals key source.code installed ready codeEq
  rw [run] at whole
  rw [tail] at suffix
  have restored := congrArg (fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>current.globals.lookup key) frame
  change post.globals.lookup key=inner.globals.lookup key at restored
  exact (congrArg Prod.snd suffix).symm.trans (restored.symm.trans (congrArg Prod.snd whole))

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.globals
#print axioms InitECandidate.Solver.Mpt.AccountDecode.reached_tail_global
