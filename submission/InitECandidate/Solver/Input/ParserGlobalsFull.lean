import InitECandidate.Solver.Input.ParserGlobals
import InitECandidate.Solver.Input.Requests.Program
import InitECandidate.Solver.Input.BytesList.OriginalCode
import InitECandidate.Solver.Input.PayloadCallTrace

namespace InitECandidate.Solver.Input.ParserGlobals
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Original byte-list parsing preserves every global except its real heap. -/
theorem bytes_list (key : MlS) (code) (installed : OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    GlobalEffects.Preserves key code BytesList.body := by
  simp only [BytesList.body,Guest.guestFn_decode_bytes_list,progToHOL]
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
    | apply GlobalEffects.scoped_body key code _ _ (ofString "ssz_split_var_list") _ _ VarList.formals VarList.body VarList.returnShape
        (DecoderRuntime.var_list_code code installed) (var_list key code installed other)

/-- All original request-list allocations, guards, loops and stores. -/
theorem requests (key : MlS) (code) (installed : OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    GlobalEffects.Preserves key code Requests.body := by
  simp only [Requests.body,Guest.guestFn_decode_requests,progToHOL]
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
    | exact GlobalEffects.call_body key code (some none) (ofString "ssz_check_offsets") _ Offsets.formals Offsets.body .one
        (Main.DecoderCall.original_offsets_code code installed) (offsets key code installed)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "alloc") _ _ PersistentAlloc.formals PersistentAlloc.body .one
        (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed other)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "ssz_fixed_list_count") _ _ FixedList.formals FixedList.body .one
        (DecoderRuntime.fixed_list_code code installed) (fixed_list key code installed)

/-- Every outcome of the entire literal original decoder preserves all
nonheap globals. In particular later hashing/verification receives the real
initialized workspace pointers and scalar globals from main. -/
theorem decoder (key : MlS) (code) (installed : OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    GlobalEffects.Preserves key code Header.body := by
  simp only [Header.body,Guest.guestFn_decode_stateless_input,progToHOL]
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
    | exact GlobalEffects.call_body key code (some none) (ofString "ssz_check_offsets") _ Offsets.formals Offsets.body .one
        (Main.DecoderCall.original_offsets_code code installed) (offsets key code installed)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "alloc") _ _ PersistentAlloc.formals PersistentAlloc.body .one
        (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed other)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "ssz_fixed_list_count") _ _ FixedList.formals FixedList.body .one
        (DecoderRuntime.fixed_list_code code installed) (fixed_list key code installed)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "decode_payload") _ _ Payload.formals Payload.body .one
        (Payload.original_code code installed) (payload key code installed other)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "decode_requests") _ _ Requests.formals Requests.body .one
        (Requests.original_code code installed) (requests key code installed other)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "decode_bytes_list") _ _ BytesList.formals BytesList.body VarList.returnShape
        (BytesList.original_code code installed) (bytes_list key code installed other)

end InitECandidate.Solver.Input.ParserGlobals

#print axioms InitECandidate.Solver.Input.ParserGlobals.bytes_list
#print axioms InitECandidate.Solver.Input.ParserGlobals.requests
#print axioms InitECandidate.Solver.Input.ParserGlobals.decoder
