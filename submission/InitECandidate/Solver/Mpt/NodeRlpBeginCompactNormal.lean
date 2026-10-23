import InitECandidate.Solver.Mpt.NodeRlpBeginCompact

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open KeyToNibbles (SpanFrame)

/-- Complete actual compact writer and size phase, retaining the real
compact length and nonwrapping final payload, with changes confined to
the fresh compact output's backing words. -/
theorem compact_phase_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag buffer pathLength : BitVec 64)
    (limit : Nat) (property : BitVec 64→BitVec 64→Prop) (data : CompactData source node tag buffer pathLength limit property)
    (fits : pathLength.toNat/2+limit+19<2^64) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source compactAndLengths=(none,target)) :
    (∃ length payload : BitVec 64,target.locals.lookup (ofString "clen")=some (.val (.word length)) ∧ length.toNat=pathLength.toNat/2+1 ∧
      target.locals.lookup (ofString "payload")=some (.val (.word payload)) ∧ pathLength.toNat/2+1≤payload.toNat ∧ payload.toNat≤pathLength.toNat/2+limit+19) ∧
      SpanFrame source target buffer (pathLength.toNat/2+1) := by
  rw [path_shapes.2.2.2.2.1] at normal
  obtain ⟨current,compactRun,lengthRun⟩:=Input.sequence_none source target compactCall lengthScope normal
  obtain ⟨next,size,nextInstalled,frame,_kept⟩:=after_compact source current node tag buffer pathLength limit property data installed compactRun
  obtain ⟨⟨payload,payloadCell,lower,upper⟩,pure⟩:=length_scope_normal current target node tag buffer next.length limit property next.value (by rw [size]; omega)
    nextInstalled next.nodeCell next.tagCell next.bufferCell next.lengthCell next.mapped lengthRun
  have saved:=(length_scope_safe (ofString "clen") (by decide) (by decide) (by decide)).summary_full current
  unfold Input.LocalSummary at saved
  rw [lengthRun] at saved
  refine ⟨⟨next.length,payload,(saved.1 rfl).trans next.lengthCell,size,payloadCell,?_,?_⟩,
    frame.trans source current target buffer _ (NibblesCompact.span_of_erase current target buffer _ pure)⟩
  · rw [size] at lower
    exact lower
  · rw [size] at upper
    omega

theorem compact_phase_safe (key : MlS) (notLength : key≠ofString "clen") (notPayload : key≠ofString "payload")
    (notEncoded : key≠ofString "el") (notValue : key≠ofString "vl") : Input.LocalPrefix key compactAndLengths := by
  rw [path_shapes.2.2.2.2.1]
  exact .seq (.call (some (ofString "clen")) _ _ (by intro name same; cases same; exact notLength))
    (length_scope_safe key notPayload notEncoded notValue)

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.compact_phase_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.compact_phase_safe
