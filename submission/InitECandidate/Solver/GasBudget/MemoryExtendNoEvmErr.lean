import InitECandidate.Solver.GasBudget.MemoryExtendProgram
import InitECandidate.Solver.GasBudget.MemoryZeroNoException
import InitECandidate.Solver.Input.NoNamedException

namespace InitECandidate.Solver.Input.NoException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem global_assign (code) (name : MlS) (expression : ExpHOL 64) : Safe code (.assign .global name expression) := by
  intro source installed identifier payload
  rw [evaluateHOLFiniteState_assign]
  repeat first | (solve | simp) | split

end InitECandidate.Solver.Input.NoException

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem trap_no_evm_error (code) : Input.NoNamedException.Safe code (ofString "EvmErr") Input.Trap.body := by
  simp only [Input.Trap.body, Guest.guestFn_trap_with, progToHOL]
  repeat first
    | apply Input.NoNamedException.sequence
    | exact Input.NoNamedException.of_all code _ _ (Input.NoException.shared_store code _ _ _)
    | exact Input.NoNamedException.of_all code _ _ (Input.NoException.external code _ _ _ _ _)
    | exact Input.NoNamedException.raised_other code _ _ _ (by decide)

theorem frame_alloc_no_evm_error (code) (installed : Input.OriginalCode.Installed code) :
    Input.NoNamedException.Safe code (ofString "EvmErr") (Arenas.body .up) := by
  simp only [Arenas.body, Guest.guestFn_frame_mem_alloc, progToHOL]
  repeat first
    | apply Input.NoNamedException.declared
    | apply Input.NoNamedException.sequence
    | apply Input.NoNamedException.conditional
    | exact Input.NoNamedException.of_all code _ _ (Input.NoException.skip code)
    | exact Input.NoNamedException.of_all code _ _ (Input.NoException.returned code _)
    | exact Input.NoNamedException.of_all code _ _ (Input.NoException.global_assign code _ _)
    | exact Input.NoNamedException.call_body code _ (ofString "trap_with") _ Input.Trap.formals Input.Trap.body .one
        (trap_code code installed) (trap_no_evm_error code)

/-- The real memory helper can trap, but cannot raise EvmErr. This covers
every clock/outcome and does not declare traps harmless or read-only. -/
theorem no_evm_error (code) (installed : Input.OriginalCode.Installed code) :
    Input.NoNamedException.Safe code (ofString "EvmErr") body := by
  simp only [body, Guest.guestFn_extend_memory, progToHOL]
  repeat first
    | apply Input.NoNamedException.declared
    | apply Input.NoNamedException.sequence
    | apply Input.NoNamedException.conditional
    | exact Input.NoNamedException.of_all code _ _ (Input.NoException.skip code)
    | exact Input.NoNamedException.of_all code _ _ (Input.NoException.returned code _)
    | exact Input.NoNamedException.of_all code _ _ (Input.NoException.assign code _ _)
    | exact Input.NoNamedException.of_all code _ _ (Input.NoException.store code _ _)
    | exact Input.NoNamedException.call_body code _ (ofString "frame_mem_alloc") _ Arenas.formals (Arenas.body .up) .one
        (alloc_code .up code installed) (frame_alloc_no_evm_error code installed)
    | exact Input.NoNamedException.of_all code _ _ (Input.NoException.call_body code (ofString "memzero") _ WitnessRadix.Zero.formals WitnessRadix.Zero.body .one
        (zero_code code installed) (zero_no_exception code))

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.Input.NoException.global_assign
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.trap_no_evm_error
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.frame_alloc_no_evm_error
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.no_evm_error
