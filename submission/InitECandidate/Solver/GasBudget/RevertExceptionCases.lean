import InitECandidate.Solver.GasBudget.RevertProgram
import InitECandidate.Solver.GasBudget.StackPopExceptionPayload
import InitECandidate.Solver.GasBudget.RegularChargeExceptionPayload
import InitECandidate.Solver.GasBudget.MemoryExtendNoEvmErr
import InitECandidate.Solver.Input.NoExceptionEventScoped

namespace InitECandidate.Solver.GasBudget.RevertOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem excludes_other_payload (code) (installed : Input.OriginalCode.Installed code) (payload : ValueHOL 64)
    (notRevert : payload ≠ .val (.word 1#64)) (notStack : payload ≠ .val (.word 2#64)) (notGas : payload ≠ .val (.word 4#64)) :
    Input.NoExceptionEvent.Safe code (ofString "EvmErr") payload body := by
  simp only [body, Guest.guestFn_op_revert, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  repeat first
    | apply Input.NoExceptionEvent.sequence
    | exact Input.NoExceptionEvent.of_all code _ _ _ (Input.NoException.store code _ _)
    | exact Input.NoExceptionEvent.of_all code _ _ _ (Input.NoException.returned code _)
    | exact Input.NoExceptionEvent.raise_literal code _ _ payload 1#64 (Ne.symm notRevert)
    | apply Input.NoExceptionEvent.scoped_body code (ofString "EvmErr") payload "start" _ (ofString "stack_pop") _ _ [] StackPop.body StackPop.shape
        (OriginalCodeEnvironment.stack_pop code installed) (StackPop.excludes_other_payload code payload notStack)
    | apply Input.NoExceptionEvent.scoped_body code (ofString "EvmErr") payload "size" _ (ofString "stack_pop") _ _ [] StackPop.body StackPop.shape
        (OriginalCodeEnvironment.stack_pop code installed) (StackPop.excludes_other_payload code payload notStack)
    | apply Input.NoExceptionEvent.scoped_body code (ofString "EvmErr") payload "x" _ (ofString "extend_memory_cost1") _ _
        MemoryCostEffects.Kind.extend_memory_cost1.signature.1 MemoryCostEffects.Kind.extend_memory_cost1.body MemoryCostEffects.Kind.extend_memory_cost1.signature.2.2
        (MemoryCostEffects.entry code installed .extend_memory_cost1)
        (Input.NoExceptionEvent.of_all code _ _ _ (MemoryCostEffects.safe_extend_memory_cost1 code installed))
    | exact Input.NoExceptionEvent.call_body code (ofString "EvmErr") (ofString "charge_gas") payload _ RegularCharge.formals RegularCharge.body .one
        (OriginalCodeEnvironment.charge_gas code installed) (RegularCharge.excludes_other_payload code payload notGas)
    | exact Input.NoExceptionEvent.of_named code _ _ _ (Input.NoNamedException.call_body code (ofString "EvmErr") (ofString "extend_memory") _
        MemoryExtend.formals MemoryExtend.body .one (MemoryExtend.original_code code installed) (MemoryExtend.no_evm_error code installed))
    | apply Input.NoExceptionEvent.scoped_body code (ofString "EvmErr") payload "n" .one (ofString "sat_word") _ _
        [(ofString "v", Input.RlpWrite.U256Value.tupleShape)] SatWord.body .one (SatWord.original_code code installed)
        (Input.NoExceptionEvent.of_all code _ _ _ (MemoryCostEffects.safe_sat_word code installed))
    | apply Input.NoExceptionEvent.scoped_body code (ofString "EvmErr") payload "s" .one (ofString "sat_word") _ _
        [(ofString "v", Input.RlpWrite.U256Value.tupleShape)] SatWord.body .one (SatWord.original_code code installed)
        (Input.NoExceptionEvent.of_all code _ _ _ (MemoryCostEffects.safe_sat_word code installed))

/-- Every actual EvmErr from unchanged REVERT is underflow, insufficient
gas, or its explicit final revert. No normal return is assumed. -/
theorem error_cases (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception (ofString "EvmErr") payload), post)) :
    payload = .val (.word 1#64) ∨ payload = .val (.word 2#64) ∨ payload = .val (.word 4#64) := by
  classical
  by_cases revert : payload = .val (.word 1#64)
  · exact Or.inl revert
  by_cases stack : payload = .val (.word 2#64)
  · exact Or.inr (Or.inl stack)
  by_cases gas : payload = .val (.word 4#64)
  · exact Or.inr (Or.inr gas)
  exact (excludes_other_payload source.code installed payload revert stack gas source rfl (congrArg Prod.fst run)).elim

end InitECandidate.Solver.GasBudget.RevertOpcode

#print axioms InitECandidate.Solver.GasBudget.RevertOpcode.excludes_other_payload
#print axioms InitECandidate.Solver.GasBudget.RevertOpcode.error_cases
