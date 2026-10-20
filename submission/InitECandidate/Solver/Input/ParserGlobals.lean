import InitECandidate.Solver.Input.DecoderRuntimeCode
import InitECandidate.Solver.Input.MainDecoderCall
import InitECandidate.Solver.WitnessRadix.AllocationGlobals

namespace InitECandidate.Solver.Input.ParserGlobals
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Original parser helpers preserve every global other than their actual
heap cursor, on all outcomes, including malformed input and failed calls. -/
theorem fail (key : MlS) (code) : GlobalEffects.Preserves key code SszFail.body := by
  rw [SszFail.body_shape]
  exact GlobalEffects.sequence key code _ _ (GlobalEffects.raised key code _ _) (GlobalEffects.returned key code _)

theorem division (key : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves key code UDivMod.body := by
  simp only [UDivMod.body,Guest.guestFn_udivmod,progToHOL]
  repeat first
    | apply GlobalEffects.sequence
    | apply GlobalEffects.conditional
    | apply GlobalEffects.declared
    | apply GlobalEffects.loop
    | exact GlobalEffects.assign key code _ _
    | exact GlobalEffects.returned key code _
    | exact GlobalEffects.skip key code
    | exact GlobalEffects.call_body key code (some none) (ofString "trap_with") _ Trap.formals Trap.body .one
        (Trap.original_code code installed) (Trap.globals key code)

theorem offsets (key : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves key code Offsets.body := by
  simp only [Offsets.body,Guest.guestFn_ssz_check_offsets,progToHOL]
  repeat first
    | apply GlobalEffects.sequence
    | apply GlobalEffects.conditional
    | apply GlobalEffects.declared
    | apply GlobalEffects.loop
    | exact GlobalEffects.assign key code _ _
    | exact GlobalEffects.returned key code _
    | exact GlobalEffects.skip key code
    | exact GlobalEffects.call_body key code (some none) (ofString "ssz_fail") _ SszFail.formals SszFail.body .one
        (Main.DecoderCall.original_fail_code code installed) (fail key code)

theorem fixed_list (key : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves key code FixedList.body := by
  simp only [FixedList.body,Guest.guestFn_ssz_fixed_list_count,progToHOL]
  repeat first
    | apply GlobalEffects.sequence
    | apply GlobalEffects.conditional
    | exact GlobalEffects.returned key code _
    | exact GlobalEffects.skip key code
    | exact GlobalEffects.call_body key code (some none) (ofString "ssz_fail") _ SszFail.formals SszFail.body .one
        (Main.DecoderCall.original_fail_code code installed) (fail key code)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "udivmod") _ _ UDivMod.formals UDivMod.body UDivMod.returnShape
        (DecoderRuntime.division_code code installed) (division key code installed)

theorem var_list (key : MlS) (code) (installed : OriginalCode.Installed code) (other : key ≠ ofString "heap_ptr") :
    GlobalEffects.Preserves key code VarList.body := by
  simp only [VarList.body,Guest.guestFn_ssz_split_var_list,progToHOL]
  repeat first
    | apply GlobalEffects.sequence
    | apply GlobalEffects.conditional
    | apply GlobalEffects.declared
    | apply GlobalEffects.loop
    | exact GlobalEffects.assign key code _ _
    | exact GlobalEffects.store key code _ _
    | exact GlobalEffects.returned key code _
    | exact GlobalEffects.skip key code
    | exact GlobalEffects.call_body key code (some none) (ofString "ssz_fail") _ SszFail.formals SszFail.body .one
        (Main.DecoderCall.original_fail_code code installed) (fail key code)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "alloc") _ _ PersistentAlloc.formals PersistentAlloc.body .one
        (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed other)

theorem payload (key : MlS) (code) (installed : OriginalCode.Installed code) (other : key ≠ ofString "heap_ptr") :
    GlobalEffects.Preserves key code Payload.body := by
  simp only [Payload.body,Scalar.payloadBody,Guest.guestFn_decode_payload,progToHOL]
  repeat first
    | apply GlobalEffects.sequence
    | apply GlobalEffects.conditional
    | apply GlobalEffects.declared
    | exact GlobalEffects.store key code _ _
    | exact GlobalEffects.returned key code _
    | exact GlobalEffects.skip key code
    | exact GlobalEffects.call_body key code (some none) (ofString "ssz_fail") _ SszFail.formals SszFail.body .one
        (Main.DecoderCall.original_fail_code code installed) (fail key code)
    | exact GlobalEffects.call_body key code (some none) (ofString "ssz_check_offsets") _ Offsets.formals Offsets.body .one
        (Main.DecoderCall.original_offsets_code code installed) (offsets key code installed)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "alloc") _ _ PersistentAlloc.formals PersistentAlloc.body .one
        (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed other)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "ssz_split_var_list") _ _ VarList.formals VarList.body VarList.returnShape
        (DecoderRuntime.var_list_code code installed) (var_list key code installed other)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "ssz_fixed_list_count") _ _ FixedList.formals FixedList.body .one
        (DecoderRuntime.fixed_list_code code installed) (fixed_list key code installed)

end InitECandidate.Solver.Input.ParserGlobals

#print axioms InitECandidate.Solver.Input.ParserGlobals.fail
#print axioms InitECandidate.Solver.Input.ParserGlobals.division
#print axioms InitECandidate.Solver.Input.ParserGlobals.offsets
#print axioms InitECandidate.Solver.Input.ParserGlobals.fixed_list
#print axioms InitECandidate.Solver.Input.ParserGlobals.var_list
#print axioms InitECandidate.Solver.Input.ParserGlobals.payload
