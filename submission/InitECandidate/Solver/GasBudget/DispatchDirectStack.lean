import InitECandidate.Solver.GasBudget.DispatchNormal
import InitECandidate.Solver.GasBudget.DirectStackOpcodeCall

namespace InitECandidate.Solver.GasBudget.DirectStackOpcode
def Kind.opcode : Kind → BitVec 64
  | .op_and => 22#64 | .op_or => 23#64 | .op_xor => 24#64 | .op_not => 25#64
end InitECandidate.Solver.GasBudget.DirectStackOpcode

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem selection_direct_stack (kind : DirectStackOpcode.Kind) :
    tree.choose kind.opcode = .invoke kind.label [] := by cases kind <;> rfl

theorem direct_stack_body_normal (kind : DirectStackOpcode.Kind)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : DirectStackOpcode.Entry source frame)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word kind.opcode)))
    (code : source.code.lookup kind.function = some ([], kind.site.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    kind.site.names.length + 4 ≤ source.clock ∧ value = .val (.word 0#64) ∧
      post.clock = source.clock - (kind.site.names.length + 4) ∧
      post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - (kind.site.names.length + 4)} ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + 3 ∧
      (wordAt post.memory (frame + 16#64)).toNat + kind.site.names.length = entry.sp.toNat + 1 ∧
      (wordAt post.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat ∧
      DirectStackOpcode.Footprint source.memory post.memory frame entry.base entry.sp kind.site.names.length ∧
      kind.site.names.length ≤ entry.sp.toNat := by
  obtain ⟨returned, function, arguments, middle, selected, helperRun, postEq⟩ := normal_helper source post kind.opcode opLocal value normal
  rw [selection_direct_stack] at selected
  cases selected
  obtain ⟨fits, clock, frameEq, budget, credit, depth, depthBound, footprint, popsFit⟩ := DirectStackOpcode.call_normal kind source middle frame entry code helperRun
  refine ⟨fits, returned, ?_, ?_, ?_, ?_, ?_, ?_, ?_, popsFit⟩
  · rw [postEq]; exact clock
  · rw [postEq]; exact congrArg emptyLocalsHOLFinite frameEq
  · rw [postEq]; exact budget
  · rw [postEq]; exact credit
  · rw [postEq]; exact depth
  · rw [postEq]; exact depthBound
  · rw [postEq]; exact footprint

/-- Full original dispatch caller for AND/OR/XOR/NOT. Every normal call
derives its available clocks, preserves the capped physical regular ledger,
credits used3 and returns a bounded stack. Actual memory/code/stack ownership
and opcode argument reachability remain entry obligations. -/
theorem direct_stack_call_normal (kind : DirectStackOpcode.Kind)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : DirectStackOpcode.Entry source frame) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word kind.opcode)])
    (dispatchCode : source.code.lookup (ofString "op_dispatch") = some (formals, body, .one))
    (code : source.code.lookup kind.function = some ([], kind.site.body, .one))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_dispatch") arguments) = (none, target)) :
    kind.site.names.length + 5 ≤ source.clock ∧ target.clock = source.clock - (kind.site.names.length + 5) ∧
      target = {source with memory := target.memory, clock := source.clock - (kind.site.names.length + 5)} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      (wordAt target.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + 3 ∧
      (wordAt target.memory (frame + 16#64)).toNat + kind.site.names.length = entry.sp.toNat + 1 ∧
      (wordAt target.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat ∧
      DirectStackOpcode.Footprint source.memory target.memory frame entry.base entry.sp kind.site.names.length ∧
      kind.site.names.length ≤ entry.sp.toNat := by
  obtain ⟨callee, called, opLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "op_dispatch") "op" body kind.opcode dispatchCode
  obtain ⟨positive, post, value, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "op_dispatch") arguments [.val (.word kind.opcode)] body callee .one args called normal
  let incoming := entry.call_entry source frame callee
  obtain ⟨fits, returned, clock, frameEq, budget, credit, depth, depthBound, footprint, popsFit⟩ :=
    direct_stack_body_normal kind (callEntryStateHOLFinite source callee) post frame incoming opLocal code value bodyRun
  rw [returned] at bodyRun
  have callerFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - (kind.site.names.length + 5)} := by
    have erased := congrArg emptyLocalsHOLFinite frameEq
    change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 1 - (kind.site.names.length + 4)} at erased
    simpa only [show source.clock - 1 - (kind.site.names.length + 4) = source.clock - (kind.site.names.length + 5) from by omega] using erased
  have actual := ignored_return source post (ofString "op_dispatch") arguments [.val (.word kind.opcode)] body callee (kind.site.names.length + 5) args called positive bodyRun callerFrame
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change target = {source with memory := post.memory, clock := source.clock - (kind.site.names.length + 5)} at same
  refine ⟨by change kind.site.names.length + 4 ≤ source.clock - 1 at fits; omega, by rw [same], ?_, ?_, ?_, ?_, ?_, ?_, popsFit⟩
  · rw [same]
  · rw [same]; exact budget
  · rw [same]; exact credit
  · rw [same]; exact depth
  · rw [same]; exact depthBound
  · rw [same]; exact footprint

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.selection_direct_stack
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.direct_stack_body_normal
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.direct_stack_call_normal
