import InitECandidate.Solver.Input.CurrentVerify.BlockSizeGuard

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Every outcome of the unchanged payload_header either stops within the
finite complete-prefix allowance or reaches its actual first indexed trie.
The reached caller retains its full physical input/header evidence, and the
actual computed-size guard supplies the accepted withdrawal-count cap. -/
theorem to_trie {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source PayloadHeader.body=(outcome,post)) :
    (source.clock-post.clock≤396931061 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ header continued inner encoded,PhysicalHeader input source continued pointer si record gasWord boundary header ∧
        encoded≤8388608 ∧ Payload.withdrawalCount input≤335544 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
        continued.locals.lookup (ofString "bl")=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
        continued.clock≤source.clock ∧ source.clock-continued.clock≤396931061 ∧ post.clock=inner.clock ∧
        evaluateHOLFiniteState continued afterSizeGuard=(outcome,inner) := by
  rcases PayloadHeader.prefix_trace source post data.arena.code outcome actual with stopped|reached
  · exact Or.inl ⟨by omega,stopped.2⟩
  · obtain ⟨current,outer,execution,forward,spent,endpoint,remaining⟩:=reached
    obtain ⟨header,physical⟩:=physical_header data execution
    rcases length_trace physical outcome remaining with stopped|reached
    · have cost:=stopped.1
      exact Or.inl ⟨by rw [endpoint]; omega,stopped.2⟩
    · obtain ⟨continued,inner,lengthExecution,nextForward,lengthCost,nextEndpoint,afterLength⟩:=reached
      obtain ⟨encoded,minimum,number,bl,retained⟩:=length_reached physical lengthExecution
      rcases size_trace continued inner input encoded minimum bl number outcome afterLength with stopped|passed
      · have cost:=stopped.1
        exact Or.inl ⟨by rw [endpoint,nextEndpoint]; omega,stopped.2⟩
      · exact Or.inr ⟨header,continued,inner,encoded,retained,passed.1,passed.2.1,number,bl,by omega,by omega,
          endpoint.trans nextEndpoint,passed.2.2⟩

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.to_trie
