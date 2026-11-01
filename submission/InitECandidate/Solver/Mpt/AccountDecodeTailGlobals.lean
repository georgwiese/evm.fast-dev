import InitECandidate.Solver.Input.MemoryEffects
import InitECandidate.Solver.Mpt.AccountDecodeTailCost
import InitECandidate.Solver.Input.GlobalEffectsScoped
import InitECandidate.Solver.WitnessRadix.ZeroCost
import InitECandidate.Solver.Input.LocalEffectsLoop

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Memory clearing changes only memory; no return or stopped outcome
changes runtime metadata. -/
theorem zero_metadata (code) : Input.MemoryMetadata.Preserves code Zero.body := by
  simp only [Zero.body,Guest.Software.guestFn_memzero,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | apply Input.MemoryMetadata.declared
    | apply Input.MemoryMetadata.sequence
    | apply Input.MemoryMetadata.conditional
    | apply Input.MemoryMetadata.loop
    | exact Input.MemoryMetadata.skip code
    | exact Input.MemoryMetadata.assign code _ _
    | exact Input.MemoryMetadata.store code _ _
    | exact Input.MemoryMetadata.byte_store code _ _
    | exact Input.MemoryMetadata.returned code _

theorem zero_globals (key : MlS) (code) : Input.GlobalEffects.Preserves key code Zero.body := by
  intro source codeEq
  have metadata:=zero_metadata code source codeEq
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change (evaluateHOLFiniteState source Zero.body).2.globals=source.globals at globals
  exact Prod.ext (Input.MemoryMetadata.code metadata) (congrArg (fun fields=>fields.lookup key) globals)

theorem nonce_loop_readonly (code) : Input.LocalEffects.Preserves code nonceLoop := by
  rw [nonce_loop_shape,nonce_body_shape]
  unfold nonceAccumulate increment
  exact Input.LocalEffects.loop code _ _
    (Input.LocalEffects.sequence code _ _ (Input.LocalEffects.assign code _ _) (Input.LocalEffects.assign code _ _))


end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.nonce_loop_readonly

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- The entire real output phase retains every runtime field except
memory, locals and clock, even on its guarding failure branches. -/
theorem after_fields_metadata (code) (installed : Input.OriginalCode.Installed code) :
    Input.MemoryMetadata.Preserves code afterFields := by
  rw [after_fields_shape,nonce_loop_shape,nonce_body_shape,after_nonce_shape,balance_phase_shape,balance_loop_shape,balance_body_shape,after_balance_shape]
  unfold nonceAccumulate increment balanceStore fail
  repeat first
    | apply Input.MemoryMetadata.declared
    | apply Input.MemoryMetadata.sequence
    | apply Input.MemoryMetadata.conditional
    | apply Input.MemoryMetadata.loop
    | exact Input.MemoryMetadata.assign code _ _
    | exact Input.MemoryMetadata.store code _ _
    | exact Input.MemoryMetadata.returned code _
    | exact Input.MemoryMetadata.skip code
    | exact Input.MemoryMetadata.call_body code (some none) (ofString "mpt_fail") _ Fail.formals Fail.body .one
        (Fail.original_code code installed) (Input.MemoryEffects.of_readonly code _ (Fail.readonly code))
    | exact Input.MemoryMetadata.call_body code (some none) (ofString "memzero") _ Zero.formals Zero.body .one
        (Zero.original_code code installed) (zero_metadata code)

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.zero_metadata
#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_fields_metadata

#print axioms InitECandidate.Solver.Mpt.AccountDecode.zero_globals

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- The stronger metadata guarantee also preserves each individual global. -/
theorem after_fields_globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) :
    Input.GlobalEffects.Preserves key code afterFields := by
  intro source codeEq
  have metadata:=after_fields_metadata code installed source codeEq
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change (evaluateHOLFiniteState source afterFields).2.globals=source.globals at globals
  exact Prod.ext (Input.MemoryMetadata.code metadata) (congrArg (fun fields=>fields.lookup key) globals)

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_fields_globals
