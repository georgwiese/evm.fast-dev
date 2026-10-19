import InitECandidate.Solver.GasBudget.ReturnExceptionCases

namespace InitECandidate.Solver.GasBudget.ReturnOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def afterCharge : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "extend_memory") [.rfield 1 (WitnessRadix.QueryBranch.localVar "x")]) afterExpansion

theorem after_charge_excludes (code) (installed : Input.OriginalCode.Installed code) (payload : ValueHOL 64)
    : Input.NoExceptionEvent.Safe code (ofString "EvmErr") payload afterCharge := by
  simp only [afterCharge, afterExpansion, afterSize, stores]
  repeat first
    | apply Input.NoExceptionEvent.sequence
    | exact Input.NoExceptionEvent.of_all code _ _ _ (Input.NoException.store code _ _)
    | exact Input.NoExceptionEvent.of_all code _ _ _ (Input.NoException.returned code _)
    | exact Input.NoExceptionEvent.of_named code _ _ _ (Input.NoNamedException.call_body code (ofString "EvmErr") (ofString "extend_memory") _
        MemoryExtend.formals MemoryExtend.body .one (MemoryExtend.original_code code installed) (MemoryExtend.no_evm_error code installed))
    | apply Input.NoExceptionEvent.scoped_body code (ofString "EvmErr") payload "n" .one (ofString "sat_word") _ _
        [(ofString "v", Input.RlpWrite.U256Value.tupleShape)] SatWord.body .one (SatWord.original_code code installed)
        (Input.NoExceptionEvent.of_all code _ _ _ (MemoryCostEffects.safe_sat_word code installed))
    | apply Input.NoExceptionEvent.scoped_body code (ofString "EvmErr") payload "s" .one (ofString "sat_word") _ _
        [(ofString "v", Input.RlpWrite.U256Value.tupleShape)] SatWord.body .one (SatWord.original_code code installed)
        (Input.NoExceptionEvent.of_all code _ _ _ (MemoryCostEffects.safe_sat_word code installed))

theorem after_cost_excludes (code) (installed : Input.OriginalCode.Installed code) (payload : ValueHOL 64)
    (notGas : payload ≠ .val (.word 4#64)) :
    Input.NoExceptionEvent.Safe code (ofString "EvmErr") payload afterCost := by
  apply Input.NoExceptionEvent.sequence
  · exact Input.NoExceptionEvent.call_body code (ofString "EvmErr") (ofString "charge_gas") payload _ RegularCharge.formals RegularCharge.body .one
      (OriginalCodeEnvironment.charge_gas code installed) (RegularCharge.excludes_other_payload code payload notGas)
  · exact after_charge_excludes code installed payload

theorem program_excludes (code) (installed : Input.OriginalCode.Installed code) (payload : ValueHOL 64)
    (notGas : payload ≠ .val (.word 4#64)) :
    Input.NoExceptionEvent.Safe code (ofString "EvmErr") payload program := by
  apply Input.NoExceptionEvent.scoped_body code (ofString "EvmErr") payload "x" _ (ofString "extend_memory_cost1") _ _
    MemoryCostEffects.Kind.extend_memory_cost1.signature.1 MemoryCostEffects.Kind.extend_memory_cost1.body MemoryCostEffects.Kind.extend_memory_cost1.signature.2.2
    (MemoryCostEffects.entry code installed .extend_memory_cost1)
    (Input.NoExceptionEvent.of_all code _ _ _ (MemoryCostEffects.safe_extend_memory_cost1 code installed))
  exact after_cost_excludes code installed payload notGas

end InitECandidate.Solver.GasBudget.ReturnOpcode

#print axioms InitECandidate.Solver.GasBudget.ReturnOpcode.after_charge_excludes
#print axioms InitECandidate.Solver.GasBudget.ReturnOpcode.after_cost_excludes
#print axioms InitECandidate.Solver.GasBudget.ReturnOpcode.program_excludes
