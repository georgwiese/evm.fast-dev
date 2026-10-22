import InitECandidate.Solver.Input.PayloadHeaderProgram
import InitECandidate.Solver.Input.CallPrefixExecution
import InitECandidate.Solver.Input.GlobalEffectsScoped
import InitECandidate.Solver.WitnessRadix.AllocationGlobals
import InitECandidate.Solver.Input.BufferGlobals
import InitECandidate.Solver.WitnessRadix.KeccakOriginalEnvironment

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

private theorem alloc_scope (key : MlS) (code) (installed : OriginalCode.Installed code) (other : key≠ofString "heap_ptr")
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
    (rest : GlobalEffects.Preserves key code tail) :
    GlobalEffects.Preserves key code (.decCall name shape (ofString "alloc") arguments tail) :=
  GlobalEffects.scoped_body key code name shape (ofString "alloc") arguments tail _ PersistentAlloc.body .one
    (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed other) rest

set_option maxRecDepth 100000 in
/-- Every original header-initialization outcome changes only the heap
global. In particular, all fixed hash/state/journal globals are retained. -/
theorem sink_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    GlobalEffects.Preserves key code (CallPrefix.program actions .skip) := by
  simp only [actions,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,CallPrefix.program]
  repeat' first
    | apply GlobalEffects.declared
    | apply GlobalEffects.sequence
    | apply alloc_scope key code installed other
    | exact GlobalEffects.store key code _ _
    | exact GlobalEffects.store_byte key code _ _
    | exact GlobalEffects.call_body key code (some none) (ofString "memzero") _ Zero.formals Zero.body .one
        (Zero.original_code code installed) (Zero.globals key code)
    | exact GlobalEffects.call_body key code (some none) (ofString "keccak256") _ Keccak256.formals Keccak256.body .one
        (Keccak256.original_code code installed) (Keccak256.globals key code (Zero.original_code code installed)
          (CopyGeneral.original_code code installed) (Keccak256.block_original_code code installed)
          (Keccak256.permutation_original_code code installed))
    | exact GlobalEffects.skip key code

theorem actual_globals (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (execution : CallPrefix.Execution source actions target)
    (key : MlS) (other : key≠ofString "heap_ptr") : target.globals.lookup key=source.globals.lookup key := by
  have preserved:=sink_globals key source.code installed other source rfl
  have known:=congrArg Prod.snd preserved
  have same:=congrArg (fun state=>state.globals.lookup key) execution.skip_erase
  exact same.symm.trans known

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.sink_globals
#print axioms InitECandidate.Solver.Input.PayloadHeader.actual_globals
