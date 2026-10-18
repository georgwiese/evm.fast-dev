import InitECandidate.Solver.GasBudget.StackPushNonGrowth
import InitECandidate.Solver.Input.UnaryCallData
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.GasBudget.StackPush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def formals : List (MlS × ShapeHOL) := [(ofString "v", .comb [.one, .one, .one, .one])]

/-- Actual ignored stack_push call on an existing free slot. Its genuine
argument lookup supplies the tuple value and formal-shape check. Funding,
body execution, caller restoration and every destination mapping are derived
from the actual normal call; no helper-run or tuple-shape premise is supplied. -/
theorem non_growth_call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base sp capacity : BitVec 64)
    (arguments : List (ExpHOL 64))
    (code : source.code.lookup (ofString "stack_push") = some (formals, body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spCell : source.memory (frame + 16#64) = .word sp) (capCell : source.memory (frame + 232#64) = .word capacity)
    (baseMapped : source.memaddrs (frame + 8#64)) (baseCell : source.memory (frame + 8#64) = .word base)
    (room : sp < capacity) (bounded : capacity.toNat ≤ 1024)
    (separate : ∀ offset ∈ ([64, 184, 192] : List Nat), ∀ index < 4,
      frame + BitVec.ofNat 64 offset ≠ (base + sp * 32#64) + BitVec.ofNat 64 (8 * index))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "stack_push") arguments) = (none, target)) :
    1 ≤ source.clock ∧ target.clock = source.clock - 1 ∧
      target = {source with memory := target.memory, clock := source.clock - 1} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      target.memory (frame + 16#64) = .word (sp + 1#64) ∧
      (wordAt target.memory (frame + 16#64)).toNat = sp.toNat + 1 ∧
      (wordAt target.memory (frame + 16#64)).toNat ≤ capacity.toNat ∧
      target.memory (frame + 184#64) = source.memory (frame + 184#64) ∧
      (∀ address, address ≠ frame + 16#64 →
        (∀ index < 4, address ≠ (base + sp * 32#64) + BitVec.ofNat 64 (8 * index)) →
        target.memory address = source.memory address) := by
  obtain ⟨positive, values, actualBody, callee, returnShape, post, returned, args, called, bodyRun, checked, postEq, fields⟩ :=
    Input.CallNormal.ignored_data source target (ofString "stack_push") arguments normal
  obtain ⟨storedValue, valuesEq, bodyEq, returnEq, valueShape, vLocal⟩ :=
    Input.CallNormal.unary_lookup_data source.code.lookup (ofString "stack_push") (ofString "v") (.comb [.one, .one, .one, .one]) body .one
      code values actualBody callee returnShape called
  rw [bodyEq] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨returnedEq, clock, frameEq, budget, spFinal, depth, usedSame, outside⟩ :=
    non_growth_normal entry post frame base sp capacity storedValue returned ev vLocal valueShape spCell capCell baseMapped baseCell room bounded separate bodyRun
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frameEq
  have canonical : target = {source with memory := post.memory, clock := source.clock - 1} := postEq.trans callerFrame
  refine ⟨positive, by rw [canonical], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [canonical]
  · rw [canonical]; exact budget
  · rw [canonical]; exact spFinal
  · rw [canonical]; exact depth
  · rw [canonical, depth]
    change sp.toNat < capacity.toNat at room
    omega
  · rw [canonical]; exact usedSame
  · intro address notSP away
    rw [canonical]
    exact outside address notSP away

end InitECandidate.Solver.GasBudget.StackPush

#print axioms InitECandidate.Solver.GasBudget.StackPush.non_growth_call_normal
