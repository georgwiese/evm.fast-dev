import InitECandidate.Solver.GasBudget.PcAddNormal

namespace InitECandidate.Solver.GasBudget.Stop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def body : ProgHOL 64 := match Guest.guestFn_op_stop with | .function fn => progToHOL fn.body | _ => .skip
def markHalted : ProgHOL 64 := .store (frameAddress 104#64) (.const 0#64)
def advance : ProgHOL 64 := .call (some (none, none)) (ofString "pc_add") [.const 1#64]

theorem body_shape : body = .seq markHalted (.seq advance (.return (.const 0#64))) := by
  simp only [body, Guest.guestFn_op_stop, progToHOL, expToHOL,
    List.map_cons, List.map_nil, Option.map_none, markHalted, advance, frameAddress]

/-- STOP is a genuine zero-charge opcode. Its actual store clears the real
running flag, so it must be counted as a terminal frame event, rather than
incorrectly assuming every opcode consumes positive regular gas. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pcCode : source.code.lookup (ofString "pc_add") = some (PcAdd.formals, PcAdd.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    1 ≤ source.clock ∧ value = .val (.word 0#64) ∧ post.clock = source.clock - 1 ∧
      post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 1} ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      post.memory (frame + 104#64) = .word 0#64 ∧
      post.memory (frame + 184#64) = source.memory (frame + 184#64) := by
  rw [body_shape] at normal
  have markSafe : Input.LocalPrefix (ofString "setup") markHalted := .store _ _
  obtain ⟨marked, markRun, restRun, _⟩ := markSafe.normal_continue source post _ value normal
  have markedEq := FrameField.normal_word source marked frame 104#64 0#64 (.const 0#64) ev rfl markRun
  have markedEV : marked.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [markedEq]; exact ev
  have markedPC : marked.code.lookup (ofString "pc_add") = some (PcAdd.formals, PcAdd.body, .one) := by rw [markedEq]; exact pcCode
  have advanceSafe : Input.LocalPrefix (ofString "setup") advance := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨advanced, advanceRun, returnRun, _⟩ := advanceSafe.normal_continue marked post _ value restRun
  obtain ⟨pc, fits, clock, mapped, pcCell, advancedEq, budget, usedSame⟩ :=
    PcAdd.call_normal marked advanced frame 1#64 [.const 1#64] rfl markedPC markedEV advanceRun
  have actualReturn : evaluateHOLFiniteState advanced (.return (.const 0#64)) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite advanced) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
  have valueEq : value = .val (.word 0#64) := by
    simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using congrArg Prod.fst (returnRun.symm.trans actualReturn)
  have postEq := congrArg Prod.snd (returnRun.symm.trans actualReturn)
  change post = emptyLocalsHOLFinite advanced at postEq
  have advancedFrame : advanced = {source with memory := advanced.memory, clock := source.clock - 1} := by
    have memoryEq := congrArg PanSemStateFiniteExact.memory advancedEq
    change advanced.memory = StoreWord.put marked.memory (frame + 0#64) (pc + 1#64) at memoryEq
    have canonical := advancedEq
    rw [← memoryEq] at canonical
    have markClock := congrArg PanSemStateFiniteExact.clock markedEq
    change marked.clock = source.clock at markClock
    rw [markClock] at canonical
    exact canonical.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
      {state with memory := advanced.memory, clock := source.clock - 1}) markedEq)
  refine ⟨by rw [markedEq] at fits; exact fits, valueEq, ?_, ?_, ?_, ?_, ?_⟩
  · rw [postEq]; change advanced.clock = _; rw [clock, markedEq]
  · rw [postEq]; exact congrArg emptyLocalsHOLFinite advancedFrame
  · rw [postEq]
    change regularBudget advanced.memory frame = _
    rw [budget, markedEq]
    exact FrameField.put_budget source.memory frame 104#64 0#64 (by decide) (by decide) (by decide)
  · rw [postEq, advancedEq]
    change StoreWord.put marked.memory (frame + 0#64) (pc + 1#64) (frame + 104#64) = _
    rw [FrameField.put_other marked.memory frame 0#64 (pc + 1#64) 104#64 (by decide), markedEq]
    simp [StoreWord.put]
  · rw [postEq]
    change advanced.memory (frame + 184#64) = _
    rw [usedSame, markedEq]
    exact FrameField.put_other source.memory frame 104#64 0#64 184#64 (by decide)

theorem call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (code : source.code.lookup (ofString "op_stop") = some ([], body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pcCode : source.code.lookup (ofString "pc_add") = some (PcAdd.formals, PcAdd.body, .one))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_stop") []) = (none, target)) :
    2 ≤ source.clock ∧ target.clock = source.clock - 2 ∧
      target = {source with memory := target.memory, clock := source.clock - 2} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      target.memory (frame + 104#64) = .word 0#64 ∧
      target.memory (frame + 184#64) = source.memory (frame + 184#64) := by
  have raw : lookupCodeHOLExact source.code.lookup (ofString "op_stop") [] = some (body, (fun _ => none), .one) := by
    simp [lookupCodeHOLExact, code]
  obtain ⟨callee, called, locals⟩ := CodeEnvironment.finite_lookup source.code.lookup (ofString "op_stop") [] body (fun _ => none) .one raw
  obtain ⟨positive, post, value, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "op_stop") [] [] body callee .one rfl called normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨fits, returned, clock, frameEq, budget, halted, usedSame⟩ := body_normal entry post frame ev pcCode value bodyRun
  rw [returned] at bodyRun
  have frame2 : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 2} := by
    have calleeFrame := congrArg emptyLocalsHOLFinite frameEq
    change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 1 - 1} at calleeFrame
    simpa only [show source.clock - 1 - 1 = source.clock - 2 from by omega] using calleeFrame
  have actual := ignored_return source post (ofString "op_stop") [] [] body callee 2 rfl called positive bodyRun frame2
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change target = {source with memory := post.memory, clock := source.clock - 2} at same
  refine ⟨by change 1 ≤ source.clock - 1 at fits; omega, by rw [same], ?_, ?_, ?_, ?_⟩
  · rw [same]
  · rw [same]; exact budget
  · rw [same]; exact halted
  · rw [same]; exact usedSame

end InitECandidate.Solver.GasBudget.Stop

#print axioms InitECandidate.Solver.GasBudget.Stop.body_shape
#print axioms InitECandidate.Solver.GasBudget.Stop.body_normal
#print axioms InitECandidate.Solver.GasBudget.Stop.call_normal
