import InitECandidate.Solver.Input.MainRunAttemptConstructorTail

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessConstructors

/-- Actual main input/startup/hash provenance is composed with the complete
unchanged run_attempt815 prefix, through header validation and both witness
databases. Errors are charged at the actual stopping stage. -/
theorem prefix_of_actual (input : Guest.InputBlob)
    (before copiedSource origin hashed source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts) (returned : RequestHash.Returned input origin hashed root)
    (entryFrame : LocalEffects.erase source=LocalEffects.erase hashed)
    (siCell : source.locals.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input))))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source RunAttempt.body=(outcome,post)) :
    source.clock-post.clock≤price input ∨ Reached input source post root outcome := by
  obtain ⟨headerArray,context,payloadCell,pointerCell,countCell,scalars,siArena,siAligned⟩ :=
    RunAttemptData.entry_data input before copiedSource origin hashed source root counts copied actual bounded prepared returned entryFrame
  have payloadAt : source.memory (byteAddress (RequestPrefix.cursor input) 0)=.word (PayloadPrefix.cursor input) := by simpa [byteAddress] using payloadCell
  rcases RunAttempt.header_prefix source post (RequestPrefix.cursor input) (PayloadPrefix.cursor input) _ _ _ _ _ _ _ _ _ _ _ _ context siArena siAligned siCell payloadAt pointerCell countCell outcome run with stopped|validated
  · exact Or.inl (stopped.trans (Nat.le_add_right _ _))
  · obtain ⟨headerTarget,first,headerReturned,remaining,headerEndpoint⟩ := validated
    have callFrame : LocalEffects.erase (validatorEntry source input)=LocalEffects.erase hashed := entryFrame
    obtain ⟨codeArray,headerSnapshot,heap,witness,nodeInputs,codeInputs,room,actualSiArena,actualSiAligned,siBefore,siLower⟩ :=
      inputs_after_headers input before copiedSource origin hashed (validatorEntry source input) headerTarget root _ counts copied actual bounded prepared returned callFrame headerReturned
    exact tail_of_inputs input source post headerTarget first root _ codeArray heap headerReturned nodeInputs codeInputs room actualSiArena actualSiAligned siBefore siLower scalars siCell
      witness.headerCountCell witness.nodePointer witness.nodeCount witness.codePointer witness.codeCount outcome remaining headerEndpoint

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.prefix_of_actual
