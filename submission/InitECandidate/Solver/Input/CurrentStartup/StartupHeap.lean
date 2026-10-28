import InitECandidate.Solver.Input.CurrentStartup.EvmHeap
import InitECandidate.Solver.Input.CurrentStartup.WorkspacePointer
import InitECandidate.Solver.Input.CurrentStartup.DecoderInput

namespace InitECandidate.Solver.Input.CurrentStartup.StartupHeap
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem routine (code) (installed : OriginalCode.Installed code) (function : Code.Routine)
    (member : function ∈ routines) : NormalHeapEffects.Returning code (Code.body function) := by
  simp only [routines, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact HeapMonotone.sha256_init code installed
  · exact HeapMonotone.keccak_init code installed
  · exact HeapMonotone.ssz_init code installed
  · exact HeapMonotone.mpt_init code installed
  · exact HeapMonotone.u256_ws_init code installed
  · exact HeapMonotone.secp256k1_init code installed
  · exact HeapMonotone.bn254_init code installed
  · exact HeapMonotone.bls_precompiles_init code installed
  · exact HeapMonotone.ripemd160_init code installed
  · exact HeapMonotone.blake2_init code installed
  · exact HeapMonotone.header_init code installed
  · exact EvmHeap.returning code installed
  · exact HeapMonotone.fork_init code installed

/-- A genuinely resuming initializer sequence retains every incoming lower
heap frontier, including its actual saved-mark release in evm_init. -/
theorem sequence (code) (installed : OriginalCode.Installed code) (functions : List Code.Routine)
    (inside : ∀ function ∈ functions, function ∈ routines) :
    NormalHeapEffects.Preserves code (withTail functions .skip) := by
  induction functions with
  | nil => exact NormalHeapEffects.skip code
  | cons function rest ih =>
    apply NormalHeapEffects.sequence code _ _
    · exact NormalHeapEffects.call_body code (some none) (Code.name function) []
        (Code.formals function) (Code.body function) (Code.shape function)
        (Code.installed code installed function) (routine code installed function (inside function (by simp))) (by unfold NormalHeapEffects.Safe; trivial)
    · exact ih (fun child member => inside child (by simp [member]))

/-- The actual main startup heap stays beyond the entire first SSZ
allocation segment. The result contains its current scalar/bound/alignment. -/
theorem main_lower (input : Guest.InputBlob) (origin target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Main.Entry input origin)
    (actual : evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip) = (none, target)) :
    NormalHeapEffects.AtLeast 2701134640 target := by
  obtain ⟨sszState, suffix, code, scalars, offsets, chunk, zeros, heap⟩ := EarlyWorkspace.main_first_three input origin target entry actual
  have initial : NormalHeapEffects.AtLeast 2701134640 sszState :=
    ⟨2701134640#64, heap, by decide, by decide, by decide⟩
  have pure := sequence sszState.code code (routines.drop 3) (fun function member => List.mem_of_mem_drop member)
  have reached := pure sszState rfl 2701134640 initial (by rw [suffix]; trivial)
  rw [suffix] at reached
  exact reached

/-- The real out/z32 allocations and remaining setup commands retain a
strong incoming lower heap frontier at the actual decoder call. -/
theorem setup_pure (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Preserves code (CallPrefix.program DecoderPrefix.setupActions .skip) := by
  simp only [DecoderPrefix.setupActions, DecoderPrefix.actions_shape, List.take_succ_cons, List.take_zero, CallPrefix.program]
  refine NormalHeapEffects.scoped_body code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (HeapMonotone.alloc code installed) ?_
  refine NormalHeapEffects.scoped_body code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (HeapMonotone.alloc code installed) ?_
  refine NormalHeapEffects.sequence code _ _
    (NormalHeapEffects.call_body code (some none) (Code.name .memzero) _
      (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
      (Code.installed code installed .memzero) (HeapMonotone.memzero code installed) (by unfold NormalHeapEffects.Safe; trivial)) ?_
  exact NormalHeapEffects.declared code _ _ _ _
    (NormalHeapEffects.declared code _ _ _ _ (NormalHeapEffects.skip code))

theorem setup_lower {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (lower : Nat)
    (installed : OriginalCode.Installed source.code) (initial : NormalHeapEffects.AtLeast lower source)
    (actual : CallPrefix.Execution source DecoderPrefix.setupActions target) : NormalHeapEffects.AtLeast lower target :=
  NormalHeapEffects.execution actual (setup_pure source.code installed) lower initial

theorem precheck_lower (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (lower : Nat)
    (installed : OriginalCode.Installed source.code) (initial : NormalHeapEffects.AtLeast lower source)
    (actual : evaluateHOLFiniteState source DecoderInput.precheck = (none, target)) : NormalHeapEffects.AtLeast lower target := by
  have pure := NormalHeapEffects.of_global source.code DecoderInput.precheck (DecoderInput.precheck_global (ofString "heap_ptr") source.code installed)
  have reached := pure source rfl lower initial (by rw [actual]; trivial)
  rw [actual] at reached
  exact reached

end InitECandidate.Solver.Input.CurrentStartup.StartupHeap

#print axioms InitECandidate.Solver.Input.CurrentStartup.StartupHeap.routine
#print axioms InitECandidate.Solver.Input.CurrentStartup.StartupHeap.sequence
#print axioms InitECandidate.Solver.Input.CurrentStartup.StartupHeap.main_lower
#print axioms InitECandidate.Solver.Input.CurrentStartup.StartupHeap.setup_pure
#print axioms InitECandidate.Solver.Input.CurrentStartup.StartupHeap.setup_lower
#print axioms InitECandidate.Solver.Input.CurrentStartup.StartupHeap.precheck_lower
