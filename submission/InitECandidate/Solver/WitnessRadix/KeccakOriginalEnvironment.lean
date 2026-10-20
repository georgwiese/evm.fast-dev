import InitECandidate.Solver.WitnessRadix.Keccak256EnvironmentFields
import InitECandidate.Solver.WitnessRadix.ZeroCost
import InitECandidate.Solver.WitnessRadix.CopyGeneralCode

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
theorem block_original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "keccak_absorb_block") = some (KeccakAbsorb.formals,KeccakAbsorb.body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 91 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_keccak_absorb_block) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,KeccakAbsorb.body,KeccakAbsorb.formals,
    Guest.guestFn_keccak_absorb_block,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem permutation_original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "keccak_f1600") = some (Keccak.formals,Keccak.f1600Body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 90 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_keccak_f1600) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Keccak.f1600Body,Keccak.formals,
    Guest.guestFn_keccak_f1600,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "keccak256") = some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 92 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_keccak256) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,
    Guest.guestFn_keccak256,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- Current installed original code, the actual oracle and two current
global bindings supply the complete hash environment. -/
theorem original_environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs = InitE.ordinaryDomain)
    (oracle : source.ffi.oracle = InitE.sourceOracle)
    (state : source.globals.lookup (ofString "keccak_st") = some (.val (.word stp)))
    (scratch : source.globals.lookup (ofString "keccak_pad") = some (.val (.word pad))) : Environment source stp pad :=
  ⟨domain,state,scratch,Zero.original_code source.code installed,CopyGeneral.original_code source.code installed,
    ⟨block_original_code source.code installed,permutation_original_code source.code installed,oracle⟩⟩

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.block_original_code
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.permutation_original_code
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.original_code
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.original_environment
