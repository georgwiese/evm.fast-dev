import InitECandidate.Solver.GasBudget.OpcodeExpNormal

namespace InitECandidate.Solver.GasBudget.OpcodeExp
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- Complete actual original EXP caller, with derived dynamic fee and
source cost<=4876. Every physical stack/gas/mutation effect is retained. -/
theorem call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : DirectStackOpcode.Entry source frame) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_exp") []) = (none, target)) :
    ∃ bytes paid, bytes ≤ 32 ∧ paid ≤ 4876 ∧ paid ≤ source.clock ∧ target.clock = source.clock - paid ∧
      target = {source with memory := target.memory, clock := source.clock - paid} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      (wordAt target.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + fee bytes ∧
      (wordAt target.memory (frame + 16#64)).toNat + 2 = entry.sp.toNat + 1 ∧
      (wordAt target.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat ∧
      DirectStackOpcode.Footprint source.memory target.memory frame entry.base entry.sp 2 ∧
      2 ≤ entry.sp.toNat := by
  have code := original_code source.code installed
  have raw : lookupCodeHOLExact source.code.lookup (ofString "op_exp") [] = some (body, (fun _ => none), .one) := by
    simp [lookupCodeHOLExact, code]
  obtain ⟨callee, called, locals⟩ := CodeEnvironment.finite_lookup source.code.lookup (ofString "op_exp") [] body (fun _ => none) .one raw
  obtain ⟨positive, post, value, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "op_exp") [] [] body callee .one rfl called normal
  let incoming := entry.call_entry source frame callee
  obtain ⟨bytes, paid, small, bounded, fits, returned, clock, frameEq, budget, credit, depth, depthBound, footprint, popsFit⟩ :=
    body_normal (callEntryStateHOLFinite source callee) post frame incoming installed value bodyRun
  rw [returned] at bodyRun
  have callerFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - (paid + 1)} := by
    change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 1 - paid} at frameEq
    simpa only [show source.clock - 1 - paid = source.clock - (paid + 1) from by omega] using frameEq
  have actual := ignored_return source post (ofString "op_exp") [] [] body callee (paid + 1) rfl called positive bodyRun callerFrame
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change target = {source with memory := post.memory, clock := source.clock - (paid + 1)} at same
  refine ⟨bytes, paid + 1, small, by omega, by change paid ≤ source.clock - 1 at fits; omega, by rw [same], ?_, ?_, ?_, ?_, ?_, ?_, popsFit⟩
  · rw [same]
  · rw [same]; exact budget
  · rw [same]; exact credit
  · rw [same]; exact depth
  · rw [same]; exact depthBound
  · rw [same]; exact footprint

end InitECandidate.Solver.GasBudget.OpcodeExp

#print axioms InitECandidate.Solver.GasBudget.OpcodeExp.call_normal
