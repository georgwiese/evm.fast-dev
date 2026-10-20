import InitECandidate.Solver.Input.MainRootAllocation

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- Same actual main run, through all initialization/parsing and the original
root allocation, now at the literal request-hashing call. The later hashing
or verification outcome remains arbitrary, with exact source scope restoration. -/
theorem root_hash_prefix_of_main (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (bounded : input.length%2^64≤Guest.maxInputBytes) (gas : Guest.GasLimit.declaredGasLimit input≤200000000)
    (result : Option (PanSemResultExact 64)) (terminal : (∃ value,result=some (.returned value)) ∨ ∃ event,result=some (.finalFfi event))
    (run : evaluateHOLFiniteState source body=(result,target)) :
    (source.clock-target.clock≤inputPrice input+(input.length%2^64)/4+DecoderCall.witnessLength input/2+1410) ∨
      ∃ before copied current root final,InputCopied input before copied ∧ DecoderCall.DecoderReady input (DecoderSetup.entered copied input) current ∧
        current.globals.lookup (Flapjack.Basis.Pure.MlString.ofString "heap_ptr")=some (.val (.word root)) ∧ root.toNat%8=0 ∧ AllocatedBytes.Arena root 32 ∧
        (RequestHash.entered current root).clock≤source.clock ∧ source.clock-(RequestHash.entered current root).clock≤inputPrice input+(input.length%2^64)/4+DecoderCall.witnessLength input/2+1360 ∧
        evaluateHOLFiniteState (RequestHash.entered current root) RequestHash.afterRoot=(result,final) ∧
        target=QueryBranch.restore before "inp" (DecoderSetup.restoration copied input (QueryBranch.restore current "root" final)) := by
  have notTimeout : result≠some .timeOut := by rcases terminal with ⟨value,same⟩ | ⟨event,same⟩ <;> rw [same] <;> simp
  rcases parsed_prefix_of_main input source target entry bounded gas result terminal run with rejected | normal
  · exact Or.inl rejected
  obtain ⟨before,copied,current,parserPost,bytes,data,forward,cost,continued,endpoint⟩ := normal
  obtain ⟨root,heap,aligned,bound,arena,funded,final,hashRun,restored⟩ := RequestHash.root_prefix input before copied current parserPost bytes data bounded result continued notTimeout
  have clock : (RequestHash.entered current root).clock=current.clock-1 := rfl
  exact Or.inr ⟨before,copied,current,root,final,bytes,data,heap,aligned,arena,by rw [clock]; omega,by rw [clock]; omega,hashRun,by rw [endpoint,restored]⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.root_hash_prefix_of_main
