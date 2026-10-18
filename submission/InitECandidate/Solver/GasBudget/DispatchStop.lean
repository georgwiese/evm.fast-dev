import InitECandidate.Solver.GasBudget.DispatchNormal
import InitECandidate.Solver.GasBudget.StopNormal

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem selection_stop : tree.choose 0#64 = .invoke "op_stop" [] := by rfl

theorem stop_body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word 0#64)))
    (code : source.code.lookup (ofString "op_stop") = some ([], Stop.body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pcCode : source.code.lookup (ofString "pc_add") = some (PcAdd.formals, PcAdd.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    2 ≤ source.clock ∧ value = .val (.word 0#64) ∧ post.clock = source.clock - 2 ∧
      post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 2} ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      post.memory (frame + 104#64) = .word 0#64 ∧
      post.memory (frame + 184#64) = source.memory (frame + 184#64) := by
  obtain ⟨returned, function, arguments, middle, selected, helperRun, postEq⟩ := normal_helper source post 0#64 opLocal value normal
  rw [selection_stop] at selected
  cases selected
  obtain ⟨fits, clock, frameEq, budget, halted, usedSame⟩ := Stop.call_normal source middle frame code ev pcCode helperRun
  refine ⟨fits, returned, ?_, ?_, ?_, ?_, ?_⟩
  · rw [postEq]; exact clock
  · rw [postEq]; exact congrArg emptyLocalsHOLFinite frameEq
  · rw [postEq]; exact budget
  · rw [postEq]; exact halted
  · rw [postEq]; exact usedSame

/-- Actual zero-opcode dispatch costs three source clocks, clears the real
running field and preserves the regular ledger. It is a terminal event even
though its irreversible gas counter does not increase. -/
theorem stop_call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word 0#64)])
    (dispatchCode : source.code.lookup (ofString "op_dispatch") = some (formals, body, .one))
    (code : source.code.lookup (ofString "op_stop") = some ([], Stop.body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pcCode : source.code.lookup (ofString "pc_add") = some (PcAdd.formals, PcAdd.body, .one))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_dispatch") arguments) = (none, target)) :
    3 ≤ source.clock ∧ target.clock = source.clock - 3 ∧
      target = {source with memory := target.memory, clock := source.clock - 3} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      target.memory (frame + 104#64) = .word 0#64 ∧
      target.memory (frame + 184#64) = source.memory (frame + 184#64) := by
  obtain ⟨callee, called, opLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "op_dispatch") "op" body 0#64 dispatchCode
  obtain ⟨positive, post, value, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "op_dispatch") arguments [.val (.word 0#64)] body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨fits, returned, clock, frameEq, budget, halted, usedSame⟩ := stop_body_normal entry post frame opLocal code ev pcCode value bodyRun
  rw [returned] at bodyRun
  have frame3 : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 3} := by
    have calleeFrame := congrArg emptyLocalsHOLFinite frameEq
    change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 1 - 2} at calleeFrame
    simpa only [show source.clock - 1 - 2 = source.clock - 3 from by omega] using calleeFrame
  have actual := ignored_return source post (ofString "op_dispatch") arguments [.val (.word 0#64)] body callee 3 args called positive bodyRun frame3
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change target = {source with memory := post.memory, clock := source.clock - 3} at same
  refine ⟨by change 2 ≤ source.clock - 1 at fits; omega, by rw [same], ?_, ?_, ?_, ?_⟩
  · rw [same]
  · rw [same]; exact budget
  · rw [same]; exact halted
  · rw [same]; exact usedSame

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.selection_stop
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.stop_body_normal
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.stop_call_normal
