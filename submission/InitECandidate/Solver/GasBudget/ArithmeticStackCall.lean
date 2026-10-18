import InitECandidate.Solver.GasBudget.ArithmeticStackNormal

namespace InitECandidate.Solver.GasBudget.ArithmeticStackOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def Kind.label : Kind → String
  | .op_add => "op_add" | .op_mul => "op_mul" | .op_sub => "op_sub" | .op_signextend => "op_signextend"
  | .op_shl => "op_shl" | .op_shr => "op_shr" | .op_sar => "op_sar"

def Kind.function (kind : Kind) : MlS := ofString kind.label

/-- Actual original arithmetic opcode caller. The concrete clocks consumed
are derived and at most bodyPrice+1, even when internal arithmetic chooses a
cheaper branch. Caller locals and every physical memory/gas/depth fact return. -/
theorem call_normal (kind : Kind) (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : DirectStackOpcode.Entry source frame) (environment : ArithmeticEffects.Environment source.code)
    (code : source.code.lookup kind.function = some ([], kind.site.body, .one))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) kind.function []) = (none, target)) :
    ∃ paid, paid ≤ kind.bodyPrice + 1 ∧ paid ≤ source.clock ∧ target.clock = source.clock - paid ∧
      target = {source with memory := target.memory, clock := source.clock - paid} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      (wordAt target.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + kind.site.fee ∧
      (wordAt target.memory (frame + 16#64)).toNat + kind.site.names.length = entry.sp.toNat + 1 ∧
      (wordAt target.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat ∧
      DirectStackOpcode.Footprint source.memory target.memory frame entry.base entry.sp kind.site.names.length ∧
      kind.site.names.length ≤ entry.sp.toNat := by
  have raw : lookupCodeHOLExact source.code.lookup kind.function [] = some (kind.site.body, (fun _ => none), .one) := by
    simp [lookupCodeHOLExact, code]
  obtain ⟨callee, called, locals⟩ := CodeEnvironment.finite_lookup source.code.lookup kind.function [] kind.site.body (fun _ => none) .one raw
  obtain ⟨positive, post, value, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target kind.function [] [] kind.site.body callee .one rfl called normal
  let incoming := entry.call_entry source frame callee
  obtain ⟨paid, bounded, fits, returned, clock, frameEq, budget, credit, depth, depthBound, footprint, popsFit⟩ :=
    body_normal kind (callEntryStateHOLFinite source callee) post frame incoming environment value bodyRun
  rw [returned] at bodyRun
  have callerFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - (paid + 1)} := by
    change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 1 - paid} at frameEq
    simpa only [show source.clock - 1 - paid = source.clock - (paid + 1) from by omega] using frameEq
  have actual := ignored_return source post kind.function [] [] kind.site.body callee (paid + 1) rfl called positive bodyRun callerFrame
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change target = {source with memory := post.memory, clock := source.clock - (paid + 1)} at same
  refine ⟨paid + 1, by omega, by change paid ≤ source.clock - 1 at fits; omega, by rw [same], ?_, ?_, ?_, ?_, ?_, ?_, popsFit⟩
  · rw [same]
  · rw [same]; exact budget
  · rw [same]; exact credit
  · rw [same]; exact depth
  · rw [same]; exact depthBound
  · rw [same]; exact footprint

end InitECandidate.Solver.GasBudget.ArithmeticStackOpcode

#print axioms InitECandidate.Solver.GasBudget.ArithmeticStackOpcode.call_normal
