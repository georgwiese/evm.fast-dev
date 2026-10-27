import InitECandidate.Solver.Input.InitializerAllocations
import InitECandidate.Solver.WitnessRadix.AllocationGlobalNormal
import InitECandidate.Solver.Input.NoneControl
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Input.InitializerAllocations
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- An observed returning initializer passed every literal global allocation
in this prefix. Failed/trapping calls cannot supply the enclosing return. -/
theorem prefix_return (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (actions : List Action)
    (tail : ProgHOL 64) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source (withTail actions tail) = (some (.returned value), target)) :
    ∃ middle, evaluateHOLFiniteState source (withTail actions .skip) = (none, middle) ∧
      evaluateHOLFiniteState middle tail = (some (.returned value), target) := by
  induction actions generalizing source with
  | nil => exact ⟨source, evaluateHOLFiniteState_skip source, actual⟩
  | cons action rest ih =>
    have safe : LocalPrefix (ofString "unused") (call action) := .globalCall _ _ _
    rw [withTail] at actual
    obtain ⟨next, firstRun, remaining⟩ := sequence_returned source target (call action) (withTail rest tail)
      value (safe.summary_full source).2.1 actual
    obtain ⟨middle, prefixRun, tailRun⟩ := ih next remaining
    refine ⟨middle, ?_, tailRun⟩
    rw [withTail, StateSteps.next_sequence source next _ _ firstRun
      (by have clock := evaluateHOLFiniteState_clock_le source (call action); rw [firstRun] at clock; exact clock)]
    exact prefixRun

/-- Invert an actual normal initializer allocation segment. Each genuine
allocation derives its own room/funding and exact post-state. No successful
future allocation or aggregate-clock/room allowance is assumed. -/
theorem normal_prefix (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (actions : List Action)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (valid : ∀ action, action ∈ actions → Valid action)
    (small : ∀ action, action ∈ actions → action.bytes < 2^64)
    (bounded : cursor ≤ 2952790016) (aligned : cursor % 8 = 0)
    (normal : evaluateHOLFiniteState source (withTail actions .skip) = (none, target)) :
    cursor + totalBytes actions ≤ 2952790016 ∧
      target = {template source cursor actions with clock := source.clock - actions.length} := by
  induction actions generalizing source cursor with
  | nil =>
    rw [withTail, evaluateHOLFiniteState_skip] at normal
    exact ⟨by simpa [totalBytes] using bounded, by simpa [template] using (congrArg Prod.snd normal).symm⟩
  | cons action rest ih =>
    have current := valid action (by simp)
    have tailValid : ∀ item, item ∈ rest → Valid item := fun item member => valid item (List.mem_cons_of_mem _ member)
    rw [withTail] at normal
    obtain ⟨middle, firstRun, suffix⟩ := sequence_none source target (call action) (withTail rest .skip) normal
    obtain ⟨old, present⟩ := scalars (ofString action.name) current.member
    have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query))
        [action.expression] = some (PersistentAlloc.values (BitVec.ofNat 64 action.bytes)) := by
      have read := current.read source
      simp only [QueryBranch.eval] at read
      simp [evalListHOLFinite, evalListHOLExact, read, PersistentAlloc.values]
    have nextAligned : (cursor + action.bytes) % 8 = 0 := by
      rw [Nat.add_mod, aligned, current.aligned]
    obtain ⟨room, nextBound, positive, postEq⟩ := PersistentAlloc.global_call_normal_expected source middle action.name old
      cursor action.bytes (cursor + action.bytes) bounded (small action (by simp))
      (Nat.le_refl _) (by omega) nextAligned present [action.expression] args
      (PersistentAlloc.original_code source.code installed) (Trap.original_code source.code installed) heap firstRun
    let next := {reserve source action cursor with clock := source.clock - 1}
    have equal : middle = next := postEq
    rw [equal] at suffix
    have nextScalars : OriginalScalarGlobals.Scalars next.globals :=
      (scalars.update (ofString "heap_ptr") (BitVec.ofNat 64 (cursor + action.bytes))).update (ofString action.name) (BitVec.ofNat 64 cursor)
    have nextHeap : next.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + action.bytes)))) := by
      simp [next, reserve, putGlobal, HolFiniteMapExact.update, FUPDATE, current.different]
    obtain ⟨tailRoom, tailEq⟩ := ih next (cursor + action.bytes) installed nextScalars nextHeap tailValid (fun item member => small item (List.mem_cons_of_mem _ member)) nextBound nextAligned suffix
    refine ⟨by simpa only [totalBytes, Nat.add_assoc] using tailRoom, ?_⟩
    rw [tailEq]
    simp only [next, template_clock, template, List.length_cons]
    congr 1
    omega

end InitECandidate.Solver.Input.InitializerAllocations

#print axioms InitECandidate.Solver.Input.InitializerAllocations.normal_prefix

#print axioms InitECandidate.Solver.Input.InitializerAllocations.prefix_return
