import InitECandidate.Solver.GasBudget.DispatchExpPrefix
import InitECandidate.Solver.GasBudget.OpcodeExpCall

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem exp_body_normal
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : DirectStackOpcode.Entry source frame) (installed : Input.OriginalCode.Installed source.code)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word 10#64)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    value = .val (.word 0#64) ∧ ∃ bytes paid, bytes ≤ 32 ∧ paid ≤ 4876 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - paid} ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + OpcodeExp.fee bytes ∧
      (wordAt post.memory (frame + 16#64)).toNat + 2 = entry.sp.toNat + 1 ∧
      (wordAt post.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat ∧
      DirectStackOpcode.Footprint source.memory post.memory frame entry.base entry.sp 2 ∧
      2 ≤ entry.sp.toNat := by
  obtain ⟨returned, function, arguments, middle, selected, helperRun, postEq⟩ := normal_helper source post 10#64 opLocal value normal
  rw [selection_exp] at selected
  cases selected
  obtain ⟨bytes, paid, small, bounded, fits, clock, frameEq, budget, credit, depth, depthBound, footprint, popsFit⟩ :=
    OpcodeExp.call_normal source middle frame entry installed helperRun
  refine ⟨returned, bytes, paid, small, bounded, fits, ?_, ?_, ?_, ?_, ?_, ?_, ?_, popsFit⟩
  · rw [postEq]; exact clock
  · rw [postEq]; exact congrArg emptyLocalsHOLFinite frameEq
  · rw [postEq]; exact budget
  · rw [postEq]; exact credit
  · rw [postEq]; exact depth
  · rw [postEq]; exact depthBound
  · rw [postEq]; exact footprint

/-- Full original EXP dispatcher caller, including variable fee, actual
bounded exponentiation and the real push/PC mutation footprint. -/
theorem exp_call_normal
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : DirectStackOpcode.Entry source frame) (installed : Input.OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word 10#64)])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_dispatch") arguments) = (none, target)) :
    ∃ bytes paid, bytes ≤ 32 ∧ paid ≤ 4877 ∧ paid ≤ source.clock ∧ target.clock = source.clock - paid ∧
      target = {source with memory := target.memory, clock := source.clock - paid} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      (wordAt target.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + OpcodeExp.fee bytes ∧
      (wordAt target.memory (frame + 16#64)).toNat + 2 = entry.sp.toNat + 1 ∧
      (wordAt target.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat ∧
      DirectStackOpcode.Footprint source.memory target.memory frame entry.base entry.sp 2 ∧
      2 ≤ entry.sp.toNat := by
  have dispatchCode := OriginalCodeEnvironment.op_dispatch source.code installed
  obtain ⟨callee, called, opLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "op_dispatch") "op" body 10#64 dispatchCode
  obtain ⟨positive, post, value, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "op_dispatch") arguments [.val (.word 10#64)] body callee .one args called normal
  let incoming := entry.call_entry source frame callee
  obtain ⟨returned, bytes, paid, small, bounded, fits, clock, frameEq, budget, credit, depth, depthBound, footprint, popsFit⟩ :=
    exp_body_normal (callEntryStateHOLFinite source callee) post frame incoming installed opLocal value bodyRun
  rw [returned] at bodyRun
  have callerFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - (paid + 1)} := by
    have erased := congrArg emptyLocalsHOLFinite frameEq
    change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 1 - paid} at erased
    simpa only [show source.clock - 1 - paid = source.clock - (paid + 1) from by omega] using erased
  have actual := ignored_return source post (ofString "op_dispatch") arguments [.val (.word 10#64)] body callee (paid + 1) args called positive bodyRun callerFrame
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change target = {source with memory := post.memory, clock := source.clock - (paid + 1)} at same
  refine ⟨bytes, paid + 1, small, by omega, by change paid ≤ source.clock - 1 at fits; omega, by rw [same], ?_, ?_, ?_, ?_, ?_, ?_, popsFit⟩
  · rw [same]
  · rw [same]; exact budget
  · rw [same]; exact credit
  · rw [same]; exact depth
  · rw [same]; exact depthBound
  · rw [same]; exact footprint

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.exp_body_normal
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.exp_call_normal
