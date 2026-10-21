import InitECandidate.Solver.Mpt.NodeConstructorProgram
import InitECandidate.Solver.WitnessRadix.AllocationGlobals
import InitECandidate.Solver.WitnessRadix.ZeroCost
import InitECandidate.Solver.Input.GlobalEffectsLoop
import InitECandidate.Solver.Input.GlobalEffectsAtoms
import InitECandidate.Solver.Input.GlobalByteEffects

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix

set_option maxRecDepth 100000 in
theorem zero_globals (key : MlS) (code) : Input.GlobalEffects.Preserves key code Zero.body := by
  simp only [Zero.body,Guest.guestFn_memzero,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | apply Input.GlobalEffects.loop
    | exact Input.GlobalEffects.assign key code _ _
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.byte_store key code _ _
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.skip key code

set_option maxRecDepth 100000 in
/-- Every original node constructor preserves the scratch/frame cursors and
all other globals apart from the genuine persistent heap update. -/
theorem globals (kind : Kind) (key : MlS) (code) (installed : Input.OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    Input.GlobalEffects.Preserves key code (body kind) := by
  rw [allocation_shape]
  apply Input.GlobalEffects.scoped_body key code (ofString "nd") .one (ofString "alloc") _ _ PersistentAlloc.formals PersistentAlloc.body .one
    (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed other)
  cases kind <;> simp only [tail,body,original,Guest.guestFn_node_new_hashed,Guest.guestFn_node_new_leaf,Guest.guestFn_node_new_ext,Guest.guestFn_node_new_branch,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  all_goals repeat first
    | apply Input.GlobalEffects.sequence
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "memzero") _ Zero.formals Zero.body .one
        (Zero.original_code code installed) (zero_globals key code)

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.zero_globals
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.globals
