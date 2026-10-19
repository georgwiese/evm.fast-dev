import InitECandidate.Solver.GasBudget.AddressMaskedBody
import InitECandidate.Solver.Input.NoExceptionLoop
import InitECandidate.Solver.Input.NoExceptionScoped

namespace InitECandidate.Solver.GasBudget.MemoryWriter
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem be32_safe (code) : Input.NoException.Safe code Kind.be32.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_st_be32, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  repeat first
    | apply Input.NoException.sequence
    | exact Input.NoException.store_byte code _ _
    | exact Input.NoException.returned code _

theorem swap_safe (code) : Input.NoException.Safe code ArithmeticEffects.Kind.bswap64.body := by
  simp only [ArithmeticEffects.Kind.body, ArithmeticEffects.Kind.signature, ArithmeticEffects.Kind.original,
    Guest.guestFn_bswap64, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  repeat first
    | apply Input.NoException.sequence
    | exact Input.NoException.assign code _ _
    | exact Input.NoException.returned code _

set_option maxHeartbeats 1000000 in
theorem be64_safe (code) (installed : Input.OriginalCode.Installed code) : Input.NoException.Safe code Kind.be64.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_st_be64, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  repeat first
    | apply Input.NoException.sequence
    | apply Input.NoException.declared
    | apply Input.NoException.conditional
    | exact Input.NoException.store code _ _
    | exact Input.NoException.returned code _
    | exact Input.NoException.skip code
    | apply Input.NoException.scoped_body code "w" .one (ofString "bswap64") _ _
        ArithmeticEffects.Kind.bswap64.signature.1 ArithmeticEffects.Kind.bswap64.body ArithmeticEffects.Kind.bswap64.signature.2.2
        (OriginalCodeEnvironment.arithmetic code installed .bswap64) (swap_safe code)
    | exact Input.NoException.call_body code (ofString "st_be32") _ _ Kind.be32.body .one (Be32Stores.original_code code installed) (be32_safe code)

end InitECandidate.Solver.GasBudget.MemoryWriter

namespace InitECandidate.Solver.GasBudget.AddressMasked
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 1000000 in
/-- Original address formatting cannot raise a source exception at any
clock/outcome. Invalid memory and timeouts are retained, not assumed absent. -/
theorem safe (code) (installed : Input.OriginalCode.Installed code) : Input.NoException.Safe code body := by
  rw [body_shape]
  apply Input.NoException.declared
  unfold stores second third
  repeat first
    | apply Input.NoException.sequence
    | exact Input.NoException.returned code _
    | exact Input.NoException.call_body code (ofString "st_be32") _ _ MemoryWriter.Kind.be32.body .one
        (Be32Stores.original_code code installed) (MemoryWriter.be32_safe code)
    | exact Input.NoException.call_body code (ofString "st_be64") _ _ MemoryWriter.Kind.be64.body .one
        (MemoryWriter.be64_code code installed) (MemoryWriter.be64_safe code installed)

end InitECandidate.Solver.GasBudget.AddressMasked

#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.be32_safe
#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.be64_safe
#print axioms InitECandidate.Solver.GasBudget.AddressMasked.safe
