import InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspaceReached
import InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame

namespace InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem later_shape : routines.drop 3 = [.mpt_init, .u256_ws_init, .secp256k1_init, .bn254_init,
    .bls_precompiles_init, .ripemd160_init, .blake2_init, .header_init, .evm_init, .fork_init] := by rfl

theorem later_body (code) (installed : OriginalCode.Installed code) (routine : Code.Routine)
    (member : routine ∈ routines.drop 3) : GlobalEffects.Preserves (ofString "ssz_offs") code (Code.body routine) := by
  rw [later_shape] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact OffsetsFrame.mpt_init code installed
  · exact OffsetsFrame.u256_ws_init code installed
  · exact OffsetsFrame.secp256k1_init code installed
  · exact OffsetsFrame.bn254_init code installed
  · exact OffsetsFrame.bls_precompiles_init code installed
  · exact OffsetsFrame.ripemd160_init code installed
  · exact OffsetsFrame.blake2_init code installed
  · exact OffsetsFrame.header_init code installed
  · exact OffsetsFrame.evm_init code installed
  · exact OffsetsFrame.fork_init code installed

/-- Every outcome of the genuine later initializer sequence retains the
SSZ offset pointer. This asserts no memory ownership or initializer runtime. -/
theorem later_prefix (code) (installed : OriginalCode.Installed code) (functions : List Code.Routine)
    (inside : ∀ routine ∈ functions, routine ∈ routines.drop 3) :
    GlobalEffects.Preserves (ofString "ssz_offs") code (withTail functions .skip) := by
  induction functions with
  | nil => exact GlobalEffects.skip (ofString "ssz_offs") code
  | cons routine rest ih =>
    apply GlobalEffects.sequence (ofString "ssz_offs") code _ _
    · exact GlobalEffects.call_body (ofString "ssz_offs") code (some none) (Code.name routine) []
        (Code.formals routine) (Code.body routine) (Code.shape routine)
        (Code.installed code installed routine) (later_body code installed routine (inside routine (by simp)))
    · exact ih (fun child member => inside child (by simp [member]))

/-- The real main startup continuation contains the actual64-byte SSZ
workspace pointer, including arbitrary mathematical input lengths. -/
theorem main_offsets (input : Guest.InputBlob) (origin target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Main.Entry input origin)
    (actual : evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip) = (none, target)) :
    target.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)) := by
  obtain ⟨sszState, suffix, code, scalars, offsets, heap⟩ := main_first_three input origin target entry actual
  have preserved := later_prefix sszState.code code (routines.drop 3) (fun routine member => member) sszState rfl
  rw [suffix] at preserved
  exact (congrArg Prod.snd preserved).trans offsets

end InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace

#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.later_shape
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.later_body
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.later_prefix
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.main_offsets
