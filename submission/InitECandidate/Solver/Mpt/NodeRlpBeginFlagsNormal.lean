import InitECandidate.Solver.Mpt.NodeRlpBeginFlags

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open KeyToNibbles (SpanFrame)

theorem after_allocation_normal_exact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag buffer pathLength : BitVec 64)
    (limit : Nat) (property : BitVec 64→BitVec 64→Prop)
    (data : CompactData (bind source "isl" 0#64) node tag buffer pathLength limit property)
    (fits : pathLength.toNat/2+limit+19<2^64) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source afterAllocation=(none,target)) :
    (∃ length payload : BitVec 64,target.locals.lookup (ofString "clen")=some (.val (.word length)) ∧ length.toNat=pathLength.toNat/2+1 ∧
      target.locals.lookup (ofString "payload")=some (.val (.word payload)) ∧ pathLength.toNat/2+1≤payload.toNat ∧ payload.toNat≤pathLength.toNat/2+limit+19 ∧ PathPayload target node tag buffer length payload) ∧
      SpanFrame source target buffer (pathLength.toNat/2+1) := by
  rw [path_shapes.2.2.1] at normal
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_none_word source target "isl" (.const 0#64) 0#64 afterLeafFlag rfl normal
  let entered:=bind source "isl" 0#64
  rw [path_shapes.2.2.2.1] at continued
  obtain ⟨current,flagRun,compactRun⟩:=Input.sequence_none entered inner leafFlag compactAndLengths continued
  obtain ⟨⟨next⟩,flagFrame⟩:=after_flag entered current node tag buffer pathLength limit property data flagRun
  have codes:=Input.LocalEffects.code_of_erase entered current flagFrame
  obtain ⟨⟨length,payload,lengthCell,size,payloadCell,lower,upper,sized⟩,compactFrame⟩:=compact_phase_normal_exact current inner node tag buffer pathLength limit property next fits
    (by rw [codes]; exact installed) compactRun
  have throughFlag:=KeyToNibbles.SpanFrame.trans entered current inner buffer (pathLength.toNat/2+1)
    (NibblesCompact.span_of_erase entered current buffer _ flagFrame) compactFrame
  have finalFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase inner:=by rw [endpoint]; rfl
  refine ⟨⟨length,payload,?_,size,?_,lower,upper,sized.of_frame finalFrame⟩,?_⟩
  · rw [endpoint,restore_lookup_other source inner "isl" "clen" (by decide)]
    exact lengthCell
  · rw [endpoint,restore_lookup_other source inner "isl" "payload" (by decide)]
    exact payloadCell
  · rw [endpoint]
    exact ⟨throughFlag.fields,throughFlag.memory⟩

theorem after_allocation_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag buffer pathLength : BitVec 64)
    (limit : Nat) (property : BitVec 64→BitVec 64→Prop)
    (data : CompactData (bind source "isl" 0#64) node tag buffer pathLength limit property)
    (fits : pathLength.toNat/2+limit+19<2^64) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source afterAllocation=(none,target)) :
    (∃ length payload : BitVec 64,target.locals.lookup (ofString "clen")=some (.val (.word length)) ∧ length.toNat=pathLength.toNat/2+1 ∧
      target.locals.lookup (ofString "payload")=some (.val (.word payload)) ∧ pathLength.toNat/2+1≤payload.toNat ∧ payload.toNat≤pathLength.toNat/2+limit+19) ∧
      SpanFrame source target buffer (pathLength.toNat/2+1) := by
  obtain ⟨⟨length,payload,cell,size,pay,lower,upper,_sized⟩,frame⟩:=after_allocation_normal_exact source target node tag buffer pathLength limit property data fits installed normal
  exact ⟨⟨length,payload,cell,size,pay,lower,upper⟩,frame⟩

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.after_allocation_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.after_allocation_normal_exact
