import InitECandidate.Solver.Input.NoExceptionLoop
import InitECandidate.Solver.WitnessRadix.ZeroProgram

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem zero_no_exception (code) : Input.NoException.Safe code WitnessRadix.Zero.body := by
  simp only [WitnessRadix.Zero.body, Guest.guestFn_memzero, progToHOL]
  repeat first
    | apply Input.NoException.declared
    | apply Input.NoException.sequence
    | apply Input.NoException.conditional
    | apply Input.NoException.loop
    | exact Input.NoException.store code _ _
    | exact Input.NoException.store_byte code _ _
    | exact Input.NoException.assign code _ _
    | exact Input.NoException.returned code _
    | exact Input.NoException.skip code

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.zero_no_exception
