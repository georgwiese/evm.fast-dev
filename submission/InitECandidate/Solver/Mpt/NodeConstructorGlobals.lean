import InitECandidate.Solver.Mpt.NodeConstructorProgram
import InitECandidate.Solver.WitnessRadix.AllocationGlobals
import InitECandidate.Solver.WitnessRadix.ZeroCost
import InitECandidate.Solver.Input.GlobalEffectsLoop
import InitECandidate.Solver.Input.GlobalEffectsAtoms
import InitECandidate.Solver.Input.GlobalByteEffects
import InitECandidate.Solver.Input.NormalHeapCall
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix

set_option maxRecDepth 100000 in
theorem zero_globals (key : MlS) (code) : Input.GlobalEffects.Preserves key code Zero.body := by
  simp only [Zero.body,Guest.Software.guestFn_memzero,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
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
  cases kind <;> simp only [tail,body,original,Guest.Software.guestFn_node_new_hashed,Guest.Software.guestFn_node_new_leaf,Guest.Software.guestFn_node_new_ext,Guest.Software.guestFn_node_new_branch,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  all_goals repeat first
    | apply Input.GlobalEffects.sequence
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "memzero") _ Zero.formals Zero.body .one
        (Zero.original_code code installed) (zero_globals key code)

set_option maxRecDepth 100000 in
/-- Each actual constructor retains the allocator's observed bounded aligned
heap through its stores and optional zeroing, including every resuming outcome. -/
theorem normal_heap (kind : Kind) (code) (installed : Input.OriginalCode.Installed code) :
    Input.NormalHeapEffects.Preserves code (body kind) := by
  rw [allocation_shape]
  apply Input.NormalHeapEffects.scoped_body code (ofString "nd") .one (ofString "alloc") _ _
    PersistentAlloc.formals PersistentAlloc.body .one (PersistentAlloc.original_code code installed)
    (PersistentAlloc.normal_heap code installed)
  cases kind <;> simp only [tail,body,original,Guest.Software.guestFn_node_new_hashed,Guest.Software.guestFn_node_new_leaf,Guest.Software.guestFn_node_new_ext,Guest.Software.guestFn_node_new_branch,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  all_goals repeat first
    | apply Input.NormalHeapEffects.sequence
    | exact Input.NormalHeapEffects.store code _ _
    | exact Input.NormalHeapEffects.returned code _
    | exact Input.NormalHeapEffects.call_body code (some none) (ofString "memzero") _ Zero.formals Zero.body .one
        (Zero.original_code code installed)
        (Input.NormalHeapEffects.of_global code Zero.body (zero_globals (ofString "heap_ptr") code)).returning (by trivial)

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.zero_globals
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.globals

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.normal_heap
