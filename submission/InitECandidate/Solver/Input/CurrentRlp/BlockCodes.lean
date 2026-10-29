import InitECandidate.Solver.Input.CurrentRlp.HeaderCall
import InitECandidate.Solver.Input.RlpLength.EntryDeclarations
import InitECandidate.Solver.Input.HeapScopeCost

namespace InitECandidate.Solver.Input.CurrentRlp.BlockLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix RlpLength

set_option maxRecDepth 100000

abbrev body:=Code.body .blockLength

theorem current_body : body=Block.body:=rfl

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "block_rlp_length")=some (Block.formals,body,.one) := by
  apply Code.installed_as code installed .blockLength
  simp only [Code.entry,Code.declaration,Code.body,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_block_rlp_length,Block.formals,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]

/-- All entries used by the real block-length tail come from the current
Software catalogue. No historical function index is reused. -/
theorem codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) : Block.Codes source := by
  refine ⟨?_,HeaderSuffix.codes source installed,HeaderSuffix.tail_codes source installed,PersistentAlloc.original_code source.code installed,
    HeapScope.mark_original_code source.code installed,HeapScope.release_original_code source.code installed,?_,?_,?_⟩
  · simpa only [HeaderEncoder.current_body] using HeaderEncoder.original_code source.code installed
  · apply Code.installed_as source.code installed .bytesLength
    simp only [Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
      Guest.Software.guestFn_rlp_bytes_encoded_len,BytesSize.formals,BytesSize.body,Guest.guestFn_rlp_bytes_encoded_len,
      paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
  · apply Code.installed_as source.code installed .withdrawalLength
    simp only [Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
      Guest.Software.guestFn_withdrawal_rlp_len,Withdrawal.formals,Withdrawal.body,Guest.guestFn_withdrawal_rlp_len,
      paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
  · apply Code.installed_as source.code installed .wordLength
    simp only [Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
      Guest.Software.guestFn_rlp_word_encoded_len,WordSize.formals,WordSize.body,Guest.guestFn_rlp_word_encoded_len,
      paramToHOL,shapeToHOL,List.map_cons,List.map_nil]

def tailPrice (input : Guest.InputBlob) (start length withdrawals : Nat) : Nat:=12*VarList.decodedCount input start length+43*withdrawals+34

def price (input : Guest.InputBlob) (start length withdrawals : Nat) : Nat:=12*VarList.decodedCount input start length+43*withdrawals+1382

end InitECandidate.Solver.Input.CurrentRlp.BlockLength

#print axioms InitECandidate.Solver.Input.CurrentRlp.BlockLength.current_body
#print axioms InitECandidate.Solver.Input.CurrentRlp.BlockLength.original_code
#print axioms InitECandidate.Solver.Input.CurrentRlp.BlockLength.codes
