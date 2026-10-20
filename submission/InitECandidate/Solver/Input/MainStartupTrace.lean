import InitECandidate.Solver.Input.MainInputEntry

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Compose every actual initializer from a specified original main run.
The caller retains that same root run, endpoint and observation while using
the reached state; the intermediate witnesses are available for memory
invariants as well as the aggregate source-clock accounting. -/
theorem startup_trace (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (result : Option (PanSemResultExact 64))
    (terminal : (∃ value,result = some (.returned value)) ∨ ∃ event,result = some (.finalFfi event))
    (rootRun : evaluateHOLFiniteState source body = (result,target)) :
    ∃ mptMiddle bnMiddle evmMiddle middle,
      MptReached source mptMiddle ∧ BnReached source mptMiddle bnMiddle ∧ EvmReached source bnMiddle evmMiddle ∧ ForkReached source evmMiddle middle ∧
      InputReady input middle ∧ evaluateHOLFiniteState middle afterFork = (result,target) := by
  have notTimeout : result ≠ some .timeOut := by
    rcases terminal with ⟨value,same⟩ | ⟨event,same⟩ <;> rw [same] <;> simp
  obtain ⟨mptMiddle,mpt,mptRun⟩ := mpt_prefix input source target entry result terminal rootRun
  obtain ⟨_,u256Run⟩ := u256_prefix input source mptMiddle target entry mpt result mptRun notTimeout
  obtain ⟨secpFunding,secpRun⟩ := secp_prefix input source mptMiddle target entry mpt result u256Run notTimeout
  obtain ⟨bnMiddle,bn,bnRun⟩ := bn_prefix input source mptMiddle target entry mpt secpFunding result secpRun notTimeout
  obtain ⟨_,blsRun⟩ := bls_prefix input source mptMiddle bnMiddle target entry mpt bn result bnRun notTimeout
  obtain ⟨_,ripemdRun⟩ := ripemd_prefix input source mptMiddle bnMiddle target entry mpt bn result blsRun notTimeout
  obtain ⟨_,blakeRun⟩ := blake_prefix input source mptMiddle bnMiddle target entry mpt bn result ripemdRun notTimeout
  obtain ⟨headerFunding,headerRun⟩ := header_prefix input source mptMiddle bnMiddle target entry mpt bn result blakeRun notTimeout
  obtain ⟨evmMiddle,evm,evmRun⟩ := evm_prefix input source mptMiddle bnMiddle target entry mpt bn headerFunding result headerRun notTimeout
  obtain ⟨middle,fork,forkRun⟩ := fork_prefix input source mptMiddle bnMiddle evmMiddle target entry mpt bn evm result evmRun notTimeout
  exact ⟨mptMiddle,bnMiddle,evmMiddle,middle,mpt,bn,evm,fork,input_ready input source mptMiddle bnMiddle evmMiddle middle entry mpt bn evm fork,forkRun⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.startup_trace
