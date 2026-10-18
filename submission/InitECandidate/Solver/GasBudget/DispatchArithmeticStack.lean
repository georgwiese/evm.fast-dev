import InitECandidate.Solver.GasBudget.DispatchNormal
import InitECandidate.Solver.GasBudget.ArithmeticStackCall

namespace InitECandidate.Solver.GasBudget.ArithmeticStackOpcode
def Kind.opcode : Kind → BitVec 64
  | .op_add => 1#64 | .op_mul => 2#64 | .op_sub => 3#64 | .op_signextend => 11#64
  | .op_shl => 27#64 | .op_shr => 28#64 | .op_sar => 29#64
end InitECandidate.Solver.GasBudget.ArithmeticStackOpcode

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem selection_arithmetic_stack (kind : ArithmeticStackOpcode.Kind) :
    tree.choose kind.opcode = .invoke kind.label [] := by cases kind <;> rfl

theorem arithmetic_stack_body_normal (kind : ArithmeticStackOpcode.Kind)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : DirectStackOpcode.Entry source frame) (environment : ArithmeticEffects.Environment source.code)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word kind.opcode)))
    (code : source.code.lookup kind.function = some ([], kind.site.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    value = .val (.word 0#64) ∧ ∃ paid, paid ≤ kind.bodyPrice + 1 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - paid} ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + kind.site.fee ∧
      (wordAt post.memory (frame + 16#64)).toNat + kind.site.names.length = entry.sp.toNat + 1 ∧
      (wordAt post.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat ∧
      DirectStackOpcode.Footprint source.memory post.memory frame entry.base entry.sp kind.site.names.length ∧
      kind.site.names.length ≤ entry.sp.toNat := by
  obtain ⟨returned, function, arguments, middle, selected, helperRun, postEq⟩ := normal_helper source post kind.opcode opLocal value normal
  rw [selection_arithmetic_stack] at selected
  cases selected
  obtain ⟨paid, bounded, fits, clock, frameEq, budget, credit, depth, depthBound, footprint, popsFit⟩ :=
    ArithmeticStackOpcode.call_normal kind source middle frame entry environment code helperRun
  refine ⟨returned, paid, bounded, fits, ?_, ?_, ?_, ?_, ?_, ?_, ?_, popsFit⟩
  · rw [postEq]; exact clock
  · rw [postEq]; exact congrArg emptyLocalsHOLFinite frameEq
  · rw [postEq]; exact budget
  · rw [postEq]; exact credit
  · rw [postEq]; exact depth
  · rw [postEq]; exact depthBound
  · rw [postEq]; exact footprint

/-- Full original dispatch caller for the seven arithmetic/shift cases.
Actual spent clocks are bounded by bodyPrice+2, while gas, physical stack
depth and complete mutation footprint retain their original meanings. -/
theorem arithmetic_stack_call_normal (kind : ArithmeticStackOpcode.Kind)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : DirectStackOpcode.Entry source frame) (environment : ArithmeticEffects.Environment source.code) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word kind.opcode)])
    (dispatchCode : source.code.lookup (ofString "op_dispatch") = some (formals, body, .one))
    (code : source.code.lookup kind.function = some ([], kind.site.body, .one))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_dispatch") arguments) = (none, target)) :
    ∃ paid, paid ≤ kind.bodyPrice + 2 ∧ paid ≤ source.clock ∧ target.clock = source.clock - paid ∧
      target = {source with memory := target.memory, clock := source.clock - paid} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      (wordAt target.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + kind.site.fee ∧
      (wordAt target.memory (frame + 16#64)).toNat + kind.site.names.length = entry.sp.toNat + 1 ∧
      (wordAt target.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat ∧
      DirectStackOpcode.Footprint source.memory target.memory frame entry.base entry.sp kind.site.names.length ∧
      kind.site.names.length ≤ entry.sp.toNat := by
  obtain ⟨callee, called, opLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "op_dispatch") "op" body kind.opcode dispatchCode
  obtain ⟨positive, post, value, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "op_dispatch") arguments [.val (.word kind.opcode)] body callee .one args called normal
  let incoming := entry.call_entry source frame callee
  obtain ⟨returned, paid, bounded, fits, clock, frameEq, budget, credit, depth, depthBound, footprint, popsFit⟩ :=
    arithmetic_stack_body_normal kind (callEntryStateHOLFinite source callee) post frame incoming environment opLocal code value bodyRun
  rw [returned] at bodyRun
  have callerFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - (paid + 1)} := by
    have erased := congrArg emptyLocalsHOLFinite frameEq
    change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 1 - paid} at erased
    simpa only [show source.clock - 1 - paid = source.clock - (paid + 1) from by omega] using erased
  have actual := ignored_return source post (ofString "op_dispatch") arguments [.val (.word kind.opcode)] body callee (paid + 1) args called positive bodyRun callerFrame
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change target = {source with memory := post.memory, clock := source.clock - (paid + 1)} at same
  refine ⟨paid + 1, by omega, by change paid ≤ source.clock - 1 at fits; omega, by rw [same], ?_, ?_, ?_, ?_, ?_, ?_, popsFit⟩
  · rw [same]
  · rw [same]; exact budget
  · rw [same]; exact credit
  · rw [same]; exact depth
  · rw [same]; exact depthBound
  · rw [same]; exact footprint

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.selection_arithmetic_stack
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.arithmetic_stack_body_normal
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.arithmetic_stack_call_normal
