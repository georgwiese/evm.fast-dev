import InitECandidate.Solver.Input.BlobCopyCost
import InitECandidate.Solver.Input.BlobCallEnvironment
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.ClockCostGuardReached
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Flapjack.Compiler.Encoders.Asm

def copyTail : ProgHOL 64 :=
  .dec (ofString "i") .one (.const 0#64) (.dec (ofString "w") .one (.const 0#64)
    (.seq copyLoop (.return (.rstruct [localVar "p", localVar "len"]))))

theorem after_guard_tail_shape : afterGuard = .decCall (ofString "p") .one (ofString "alloc")
    [addConst (localVar "len") 8#64] copyTail := after_guard_shape

theorem copy_tail_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length ≤ 1073741808)
    (limit : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock - (evaluateHOLFiniteState source copyTail).2.clock ≤ (length + 7) / 8 := by
  let withI := bind source "i" 0#64
  let ready := bind withI "w" 0#64
  have current : ready.locals.lookup (ofString "i") = some (.val (.word 0#64)) :=
    (bind_lookup_other withI "w" "i" 0#64 (by decide)).trans (bind_lookup_same _ _ _)
  have saved : ready.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))) :=
    (bind_lookup_other withI "w" "len" 0#64 (by decide)).trans
      ((bind_lookup_other source "i" "len" 0#64 (by decide)).trans limit)
  have loopCost := copy_loop_cost ready length 0#64 small current saved (by simp)
  have suffix := ClockCost.sequence_current ready copyLoop
    (.return (.rstruct [localVar "p", localVar "len"])) ((length + 7) / 8) 0
    (by simpa using loopCost) (ClockCost.returned ready.code _)
  rw [copyTail]
  apply ClockCost.declared_current source "i" (.const 0#64) 0#64 _ _ rfl
  apply ClockCost.declared_current withI "w" (.const 0#64) 0#64 _ _ rfl
  simpa only [Nat.add_zero] using suffix

/-- The allocator's actual return reinstalls the saved length. Its failure
paths are included without requiring room, a returned pointer or future copy. -/
theorem after_guard_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length ≤ 1073741808) (installed : OriginalCode.Installed source.code)
    (limit : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock - (evaluateHOLFiniteState source afterGuard).2.clock ≤ (length + 7) / 8 + 2 := by
  let amount := BitVec.ofNat 64 length + 8#64
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [addConst (localVar "len") 8#64] = some (WitnessRadix.PersistentAlloc.values amount) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, addConst,
      limit, valueWord, valueIsWord, wordOpHOL, wordOp, WitnessRadix.PersistentAlloc.values, amount]
  obtain ⟨callee, called, _⟩ := WitnessRadix.PersistentAlloc.environment source.code.lookup amount
    (WitnessRadix.PersistentAlloc.original_code source.code installed)
  have price := ClockCost.scoped_reached_current source "p" .one (ofString "alloc")
    [addConst (localVar "len") 8#64] (WitnessRadix.PersistentAlloc.values amount)
    WitnessRadix.PersistentAlloc.body copyTail callee .one 1 ((length + 7) / 8) args called
    (WitnessRadix.PersistentAlloc.body_price source.code installed _ rfl) ?_
  · rw [after_guard_tail_shape]
    omega
  · intro target returned normal checked
    have saved : (CallNormal.continuationEntry source target "p" returned).locals.lookup (ofString "len") =
        some (.val (.word (BitVec.ofNat 64 length))) := by
      simpa [CallNormal.continuationEntry, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "p" ≠ ofString "len" from by decide] using limit
    exact copy_tail_cost _ length small saved

theorem guard_pass_length (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (limit : source.locals.lookup (ofString "len") = some (.val (.word word)))
    (passed : evaluateHOLFiniteState source guard = (none, source)) : word.toNat ≤ 1073741808 := by
  have read : eval source oversized =
      some (.val (.word (if 1073741808 < word.toNat then 1#64 else 0#64))) := by
    simp [eval, oversized, localVar, evalHOLExact, limit, wordCmpHOL, BitVec.lt_def]
  simp only [eval] at read
  by_cases bad : 1073741808 < word.toNat
  · rw [guard, evaluateHOLFiniteState_ite, read] at passed
    simp only [if_pos bad, show (1#64) ≠ 0 from by decide, ↓reduceIte] at passed
    have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
        [.const 8#64] = some (Trap.values 8#64) := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, Trap.values]
    exact (Trap.call_not_normal source source _ 8#64 (Trap.original_code source.code installed) args passed).elim
  · omega

theorem guarded_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (limit : source.locals.lookup (ofString "len") = some (.val (.word word))) :
    source.clock - (evaluateHOLFiniteState source (.seq guard afterGuard)).2.clock ≤ 134217728 := by
  have stops : (evaluateHOLFiniteState source
      (.call (some (none, none)) (ofString "trap_with") [.const 8#64])).1 ≠ none := by
    intro normal
    have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
        [.const 8#64] = some (Trap.values 8#64) := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, Trap.values]
    exact Trap.call_not_normal source _ _ 8#64 (Trap.original_code source.code installed) args (Prod.ext normal rfl)
  have cost := ClockCost.stopping_guard_reached source oversized
    (.call (some (none, none)) (ofString "trap_with") [.const 8#64]) afterGuard 1 134217728 stops
    (Trap.call_price source.code installed _ source rfl) ?_
  · exact cost
  · intro passed
    have small := guard_pass_length source word installed limit passed
    have price := after_guard_cost source word.toNat small installed
      (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using limit)
    omega

/-- Every outcome of the current input_blob body is bounded from installed
code alone. The length and its guard are derived from actual execution. This
counts source call/loop ticks, not target instructions or a whole-program K. -/
theorem body_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code body 134217728 := by
  intro source codeEq
  let ready := bind source "len" 0#64
  have back : ∀ middle, evaluateHOLFiniteState ready loadLength = (none, middle) →
      middle.clock - (evaluateHOLFiniteState middle (.seq guard afterGuard)).2.clock ≤ 134217728 := by
    intro middle normal
    obtain ⟨word, cell⟩ := shared_load_normal_word ready middle (ofString "len") .opW (.const 1073741832#64) normal
    have preserved := (Input.evaluation_fields ready middle loadLength none normal).2.2.2
    have installedNow : OriginalCode.Installed middle.code := by
      rw [preserved]
      change OriginalCode.Installed source.code
      rw [codeEq]
      exact installed
    exact guarded_cost middle word installedNow cell
  have priced := ClockCost.sequence_reached_current ready loadLength (.seq guard afterGuard) 0 134217728
    (ClockCost.shared_load ready.code _ _ _ _ ready rfl) back
  rw [body_shape]
  apply ClockCost.declared_current source "len" (.const 0#64) 0#64 _ _ rfl
  simpa only [Nat.zero_add] using priced

theorem call_cost (code) (installed : OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination) (ofString "input_blob") arguments) 134217729 :=
  ClockCost.call_body code destination _ arguments [] body returnShape 134217728
    (original_code code installed) (body_cost code installed)

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.copy_tail_cost
#print axioms InitECandidate.Solver.Input.Blob.after_guard_cost
#print axioms InitECandidate.Solver.Input.Blob.guard_pass_length
#print axioms InitECandidate.Solver.Input.Blob.guarded_cost
#print axioms InitECandidate.Solver.Input.Blob.body_cost
#print axioms InitECandidate.Solver.Input.Blob.call_cost
