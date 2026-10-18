import InitECandidate.Solver.GasBudget.DispatchNormal
import InitECandidate.Solver.GasBudget.JumpdestNormal

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem selection_jumpdest : tree.choose 91#64 = .invoke "op_jumpdest" [] := by rfl

theorem jumpdest_body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word 91#64)))
    (code : source.code.lookup (ofString "op_jumpdest") = some ([], Jumpdest.body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (chargeCode : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one))
    (pcCode : source.code.lookup (ofString "pc_add") = some (PcAdd.formals, PcAdd.body, .one))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    3 ≤ source.clock ∧ value = .val (.word 0#64) ∧ post.clock = source.clock - 3 ∧
      post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 3} ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + 1 := by
  obtain ⟨returned, function, arguments, middle, selected, helperRun, postEq⟩ := normal_helper source post 91#64 opLocal value normal
  rw [selection_jumpdest] at selected
  cases selected
  obtain ⟨fits, clock, frameEq, budget, credit⟩ := Jumpdest.call_normal source middle frame code ev chargeCode pcCode cap helperRun
  refine ⟨fits, returned, ?_, ?_, ?_, ?_⟩
  · rw [postEq]; exact clock
  · rw [postEq]
    exact congrArg emptyLocalsHOLFinite frameEq
  · rw [postEq]; exact budget
  · rw [postEq]; exact credit

/-- Actual opcode91 dispatch, including the outer op_dispatch call. Four
source clocks are derived and the real irreversible regular counter grows
by one while the full physical regular budget remains equal. -/
theorem jumpdest_call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word 91#64)])
    (dispatchCode : source.code.lookup (ofString "op_dispatch") = some (formals, body, .one))
    (code : source.code.lookup (ofString "op_jumpdest") = some ([], Jumpdest.body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (chargeCode : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one))
    (pcCode : source.code.lookup (ofString "pc_add") = some (PcAdd.formals, PcAdd.body, .one))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_dispatch") arguments) = (none, target)) :
    4 ≤ source.clock ∧ target.clock = source.clock - 4 ∧
      target = {source with memory := target.memory, clock := source.clock - 4} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      (wordAt target.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + 1 := by
  obtain ⟨callee, called, opLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "op_dispatch") "op" body 91#64 dispatchCode
  obtain ⟨positive, post, value, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "op_dispatch") arguments [.val (.word 91#64)] body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨fits, returned, clock, frameEq, budget, credit⟩ := jumpdest_body_normal entry post frame opLocal code ev chargeCode pcCode cap value bodyRun
  rw [returned] at bodyRun
  have frame4 : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 4} := by
    have calleeFrame := congrArg emptyLocalsHOLFinite frameEq
    change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 1 - 3} at calleeFrame
    simpa only [show source.clock - 1 - 3 = source.clock - 4 from by omega] using calleeFrame
  have actual := ignored_return source post (ofString "op_dispatch") arguments [.val (.word 91#64)] body callee 4 args called positive bodyRun frame4
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change target = {source with memory := post.memory, clock := source.clock - 4} at same
  refine ⟨by change 3 ≤ source.clock - 1 at fits; omega, by rw [same], ?_, ?_, ?_⟩
  · rw [same]
  · rw [same]; exact budget
  · rw [same]; exact credit

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.selection_jumpdest
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.jumpdest_body_normal
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.jumpdest_call_normal
