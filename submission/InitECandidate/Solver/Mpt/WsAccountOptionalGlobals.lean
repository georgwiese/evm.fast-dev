import InitECandidate.Solver.Mpt.WsAccountOptionalProgram
import InitECandidate.Solver.Mpt.AccountDecodeGlobals
import InitECandidate.Solver.Mpt.LookupGlobals
import InitECandidate.Solver.PanHeapGlobals

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

set_option maxRecDepth 10000 in
/-- All original provider outcomes preserve every global other than its
temporary/persistent heap and scratch cursors. Actual helper metadata and
effects are used, including the complete unchanged account decoder. -/
theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code)
    (notHeap : key≠ofString "heap_ptr") (notScratch : key≠ofString "scratch_ptr") :
    Input.GlobalEffects.Preserves key code body := by
  rw [body_shape,after_leaf_shape,after_guard_shape,after_alloc_shape]
  repeat first
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | exact Input.GlobalEffects.skip key code
    | exact Input.GlobalEffects.returned key code _
    | apply Input.GlobalEffects.scoped_body key code (ofString "leaf") TrieWalk.resultShape (ofString "ws_account_leaf") _ _ WsAccountLeaf.formals WsAccountLeaf.body TrieWalk.resultShape
        (WsAccountLeaf.original_code code installed) (WsAccountLeaf.globals key code installed notHeap)
    | apply Input.GlobalEffects.scoped_body key code (ofString "a") .one (ofString "alloc") _ _ PersistentAlloc.formals PersistentAlloc.body .one
        (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed notHeap)
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "decode_account_from_leaf") decodeArguments AccountDecode.formals AccountDecode.body .one
        (AccountDecode.original_code code installed) (AccountDecode.globals key code installed notHeap notScratch)

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.globals
