import InitECandidate.Solver.GasBudget.PcAddNormal
import InitECandidate.Solver.GasBudget.RegularChargeNormalCall

namespace InitECandidate.Solver.GasBudget.Jumpdest
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def body : ProgHOL 64 := match Guest.guestFn_op_jumpdest with | .function fn => progToHOL fn.body | _ => .skip
def charge : ProgHOL 64 := .call (some (none, none)) (ofString "charge_gas") [.const 1#64]
def advance : ProgHOL 64 := .call (some (none, none)) (ofString "pc_add") [.const 1#64]

theorem body_shape : body = .seq charge (.seq advance (.return (.const 0#64))) := by
  simp only [body, Guest.guestFn_op_jumpdest, progToHOL, expToHOL,
    List.map_cons, List.map_nil, Option.map_none, charge, advance]

/-- The original successful JUMPDEST performs its real unit charge before
pc_add. Both helper clocks and the exact used-counter increment follow from
the actual normal execution, rather than a supplied execution trace. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (chargeCode : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one))
    (pcCode : source.code.lookup (ofString "pc_add") = some (PcAdd.formals, PcAdd.body, .one))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    2 ≤ source.clock ∧ value = .val (.word 0#64) ∧ post.clock = source.clock - 2 ∧
      post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 2} ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + 1 := by
  rw [body_shape] at normal
  have chargeSafe : Input.LocalPrefix (ofString "setup") charge := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨charged, chargeRun, restRun, _⟩ := chargeSafe.normal_continue source post _ value normal
  obtain ⟨gas, used, chargeFits, chargeClock, gasMapped, usedMapped, gasCell, usedCell, affordable, chargeFrame, chargeBudget, debit, credit⟩ :=
    RegularCharge.call_normal source charged frame 1#64 [.const 1#64] rfl chargeCode ev cap chargeRun
  have chargedEV : charged.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [chargeFrame]; exact ev
  have chargedPC : charged.code.lookup (ofString "pc_add") = some (PcAdd.formals, PcAdd.body, .one) := by rw [chargeFrame]; exact pcCode
  have advanceSafe : Input.LocalPrefix (ofString "setup") advance := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨advanced, advanceRun, returnRun, _⟩ := advanceSafe.normal_continue charged post _ value restRun
  obtain ⟨pc, pcFits, pcClock, pcMapped, pcCell, pcFrame, pcBudget, usedSame⟩ :=
    PcAdd.call_normal charged advanced frame 1#64 [.const 1#64] rfl chargedPC chargedEV advanceRun
  have actualReturn : evaluateHOLFiniteState advanced (.return (.const 0#64)) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite advanced) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
  have valueEq : value = .val (.word 0#64) := by
    simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using congrArg Prod.fst (returnRun.symm.trans actualReturn)
  have postEq := congrArg Prod.snd (returnRun.symm.trans actualReturn)
  change post = emptyLocalsHOLFinite advanced at postEq
  have fullFrame : advanced = {source with memory := advanced.memory, clock := source.clock - 2} := by
    have same := pcFrame.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
      {state with memory := StoreWord.put charged.memory (frame + 0#64) (pc + 1#64), clock := charged.clock - 1}) chargeFrame)
    have memoryEq := congrArg PanSemStateFiniteExact.memory pcFrame
    change advanced.memory = StoreWord.put charged.memory (frame + 0#64) (pc + 1#64) at memoryEq
    rw [← memoryEq, chargeClock] at same
    simpa only [show source.clock - 1 - 1 = source.clock - 2 from by omega] using same
  refine ⟨by omega, valueEq, ?_, ?_, ?_, ?_⟩
  · rw [postEq]; change advanced.clock = _; omega
  · rw [postEq]
    exact congrArg emptyLocalsHOLFinite fullFrame
  · rw [postEq]
    exact pcBudget.trans chargeBudget
  · rw [postEq]
    change (MemoryBytes.wordBits (advanced.memory (frame + 184#64))).toNat = _
    rw [usedSame]
    change (wordAt charged.memory (frame + 184#64)).toNat = _
    rw [credit]
    simp only [wordAt, usedCell, MemoryBytes.wordBits]
    rfl

theorem call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (code : source.code.lookup (ofString "op_jumpdest") = some ([], body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (chargeCode : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one))
    (pcCode : source.code.lookup (ofString "pc_add") = some (PcAdd.formals, PcAdd.body, .one))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_jumpdest") []) = (none, target)) :
    3 ≤ source.clock ∧ target.clock = source.clock - 3 ∧
      target = {source with memory := target.memory, clock := source.clock - 3} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      (wordAt target.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + 1 := by
  have raw : lookupCodeHOLExact source.code.lookup (ofString "op_jumpdest") [] = some (body, (fun _ => none), .one) := by
    simp [lookupCodeHOLExact, code]
  obtain ⟨callee, called, locals⟩ := CodeEnvironment.finite_lookup source.code.lookup (ofString "op_jumpdest") [] body (fun _ => none) .one raw
  obtain ⟨positive, post, value, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "op_jumpdest") [] [] body callee .one rfl called normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨fits, returned, clock, frameEq, budget, credit⟩ := body_normal entry post frame ev chargeCode pcCode cap value bodyRun
  rw [returned] at bodyRun
  have frame3 : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 3} := by
    have calleeFrame := congrArg emptyLocalsHOLFinite frameEq
    change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 1 - 2} at calleeFrame
    have sub : source.clock - 1 - 2 = source.clock - 3 := by omega
    simpa only [sub] using calleeFrame
  have actual := ignored_return source post (ofString "op_jumpdest") [] [] body callee 3 rfl called positive bodyRun frame3
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change target = {source with memory := post.memory, clock := source.clock - 3} at same
  refine ⟨by change 2 ≤ source.clock - 1 at fits; omega, by rw [same], ?_, ?_, ?_⟩
  · rw [same]
  · rw [same]; exact budget
  · rw [same]; exact credit

end InitECandidate.Solver.GasBudget.Jumpdest

#print axioms InitECandidate.Solver.GasBudget.Jumpdest.body_shape
#print axioms InitECandidate.Solver.GasBudget.Jumpdest.body_normal
#print axioms InitECandidate.Solver.GasBudget.Jumpdest.call_normal
