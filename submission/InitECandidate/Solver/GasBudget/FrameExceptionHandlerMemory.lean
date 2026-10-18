import InitECandidate.Solver.GasBudget.FrameExceptionMemoryFrame
import InitECandidate.Solver.GasBudget.FrameExceptionHandler
import InitECandidate.Solver.GasBudget.FrameRank

namespace InitECandidate.Solver.GasBudget.FrameException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem handler_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (view : View source) (err : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (errLocal : source.locals.lookup (ofString "err") = some (.val (.word err)))
    (normal : evaluateHOLFiniteState source RunFrames.opcodeHandler = (none, target)) :
    target.memory = memoryAfter source.memory view.frame view.continuation err view.empty view.gas view.spill view.reservoir := by
  obtain ⟨positive, values, actual, callee, shape, post, returned, args, called, bodyRun, checked, postEq, fields⟩ :=
    Input.CallNormal.ignored_data source target (ofString "frame_exception") [localVar "err"] normal
  obtain ⟨argument, valuesEq, bodyEq, shapeEq, typed, binding⟩ := Input.CallNormal.unary_lookup_data source.code.lookup
    (ofString "frame_exception") (ofString "err") .one body .one (original_code source.code installed)
    values actual callee shape called
  rw [valuesEq] at args
  have read := Input.single_argument source (localVar "err") argument args
  have expected : eval source (localVar "err") = some (.val (.word err)) := by
    simp [eval, localVar, evalHOLExact, toExact, errLocal]
  have argumentEq : argument = .val (.word err) := Option.some.inj (read.symm.trans expected)
  rw [argumentEq] at binding
  rw [bodyEq] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  let current := view.after_prefix (StackPop.PrefixEffect.call_entry source callee view.frame positive)
  have exactMemory := body_memory entry post current err installed binding returned bodyRun
  change post.memory = memoryAfter source.memory view.frame view.continuation err view.empty view.gas view.spill view.reservoir at exactMemory
  rw [postEq]
  exact exactMemory

theorem handler_used_monotone (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (view : View source) (err : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (errLocal : source.locals.lookup (ofString "err") = some (.val (.word err)))
    (normal : evaluateHOLFiniteState source RunFrames.opcodeHandler = (none, target)) :
    (wordAt source.memory (view.frame + 184#64)).toNat ≤ (wordAt target.memory (view.frame + 184#64)).toNat := by
  rw [handler_memory source target view err installed errLocal normal]
  exact memory_after_used source.memory view.frame view.continuation err view.empty view.gas view.spill view.reservoir
    view.gasCell view.spillCell (view.continuationAway 184 (by simp)) view.cap

/-- The actual terminal handler conserves the complete physical live budget
and never decreases its live used sum, under current frame/continuation
separation from the ancestor gas words. -/
theorem handler_sums (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (view : View source) (err : BitVec 64)
    (ancestors : List (BitVec 64))
    (apart : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      (∀ field ∈ writeOffsets, ancestor + BitVec.ofNat 64 offset ≠ view.frame + BitVec.ofNat 64 field) ∧
      ancestor + BitVec.ofNat 64 offset ≠ view.continuation + 32#64)
    (installed : Input.OriginalCode.Installed source.code)
    (errLocal : source.locals.lookup (ofString "err") = some (.val (.word err)))
    (normal : evaluateHOLFiniteState source RunFrames.opcodeHandler = (none, target)) :
    FrameSums.budget target.memory (view.frame :: ancestors) = FrameSums.budget source.memory (view.frame :: ancestors) ∧
      FrameSums.used source.memory (view.frame :: ancestors) ≤ FrameSums.used target.memory (view.frame :: ancestors) ∧
      target.memory (view.continuation + 32#64) = .word 1#64 := by
  have memoryEq := handler_memory source target view err installed errLocal normal
  have ancestorWords : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      target.memory (ancestor + BitVec.ofNat 64 offset) = source.memory (ancestor + BitVec.ofNat 64 offset) := by
    intro ancestor member offset inside
    rw [memoryEq]
    exact memory_after_away source.memory view.frame view.continuation err view.empty view.gas view.spill view.reservoir _
      (apart ancestor member offset inside).1 (apart ancestor member offset inside).2
  have ancestorBudget := FrameSums.budget_congr source.memory target.memory ancestors ancestorWords
  have ancestorUsed := FrameSums.used_congr source.memory target.memory ancestors (by intro ancestor member; exact ancestorWords ancestor member 184 (by simp))
  obtain ⟨funded, price, clock, canonical, parentBudget, done⟩ := handler_normal source target view err installed errLocal normal
  have parentUsed := handler_used_monotone source target view err installed errLocal normal
  refine ⟨?_, ?_, done⟩
  · change regularBudget target.memory view.frame + FrameSums.budget target.memory ancestors = regularBudget source.memory view.frame + FrameSums.budget source.memory ancestors
    rw [parentBudget, ancestorBudget]
  · change (wordAt source.memory (view.frame + 184#64)).toNat + FrameSums.used source.memory ancestors ≤
      (wordAt target.memory (view.frame + 184#64)).toNat + FrameSums.used target.memory ancestors
    rw [ancestorUsed]
    omega

/-- Actual handler completion discharges the terminal rank case once the
current physical live budget and ownership are supplied. -/
theorem handler_rank (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (view : View source) (err : BitVec 64)
    (ancestors : List (BitVec 64)) (limit : Nat)
    (apart : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      (∀ field ∈ writeOffsets, ancestor + BitVec.ofNat 64 offset ≠ view.frame + BitVec.ofNat 64 field) ∧
      ancestor + BitVec.ofNat 64 offset ≠ view.continuation + 32#64)
    (cap : FrameSums.budget source.memory (view.frame :: ancestors) ≤ limit)
    (installed : Input.OriginalCode.Installed source.code)
    (errLocal : source.locals.lookup (ofString "err") = some (.val (.word err)))
    (normal : evaluateHOLFiniteState source RunFrames.opcodeHandler = (none, target)) :
    FrameRank.value limit target.memory (view.frame :: ancestors) false < FrameRank.value limit source.memory (view.frame :: ancestors) true ∧
      target.memory (view.continuation + 32#64) = .word 1#64 := by
  obtain ⟨budget, used, done⟩ := handler_sums source target view err ancestors apart installed errLocal normal
  have bounded : FrameSums.used target.memory (view.frame :: ancestors) ≤ limit := by
    apply (FrameSums.used_le_budget target.memory (view.frame :: ancestors)).trans
    rw [budget]
    exact cap
  exact ⟨FrameRank.terminal limit source.memory target.memory _ _ (by simp) used bounded rfl, done⟩

end InitECandidate.Solver.GasBudget.FrameException

#print axioms InitECandidate.Solver.GasBudget.FrameException.handler_memory
#print axioms InitECandidate.Solver.GasBudget.FrameException.handler_used_monotone
#print axioms InitECandidate.Solver.GasBudget.FrameException.handler_sums
#print axioms InitECandidate.Solver.GasBudget.FrameException.handler_rank
