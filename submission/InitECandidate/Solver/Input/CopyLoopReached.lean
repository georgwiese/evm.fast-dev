import InitECandidate.Solver.Input.CopyStepReached
import InitECandidate.Solver.Input.BlobCopyCost

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Mappings and host presence observed in a completed sequence of real copy
iterations. This is a conclusion about those reads/stores, not a future promise. -/
def ObservedWords (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (index rounds : Nat) : Prop :=
  ∀ slot < rounds, source.memaddrs (pointer + BitVec.ofNat 64 (index + 8 * slot)) ∧
    ∀ byte < 8, (source.ffi.ffiState
      (Guest.inputDataAddr + BitVec.ofNat 64 (index + 8 * slot) + BitVec.ofNat 64 byte)).isSome = true

/-- A real completed copy loop determines its exact state and every accessed
word. There are no future readability, store-success or clock-funding premises. -/
theorem copy_loop_reached (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer old : BitVec 64) (index length rounds : Nat)
    (small : length + 8 < 2^64)
    (lower : length ≤ index + 8 * rounds) (upper : index + 8 * rounds < length + 8)
    (pointerLocal : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))))
    (wordLocal : source.locals.lookup (ofString "w") = some (.val (.word old)))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (normal : evaluateHOLFiniteState source copyLoop = (none, target)) :
    target = walk source pointer index rounds ∧ ObservedWords source pointer index rounds := by
  classical
  induction rounds generalizing source target index old with
  | zero =>
    have read := copy_test source index length (by omega) (by omega) indexLocal lengthLocal
    have inactive : ¬ index < length := by omega
    rw [if_neg inactive] at read
    change evalHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      copyCondition = some (.val (.word 0#64)) at read
    rw [copyLoop, evaluateHOLFiniteState_while_total, read] at normal
    simp only [ne_eq, not_true_eq_false, ↓reduceIte] at normal
    exact ⟨(congrArg Prod.snd normal).symm, by intro slot inside; omega⟩
  | succ rounds ih =>
    have active : index < length := by omega
    have read := copy_test source index length (by omega) (by omega) indexLocal lengthLocal
    rw [if_pos active] at read
    change evalHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      copyCondition = some (.val (.word 1#64)) at read
    rw [copyLoop, evaluateHOLFiniteState_while_total, read] at normal
    simp only [show (1#64) ≠ 0 from by decide, ↓reduceIte] at normal
    by_cases zero : source.clock = 0
    · rw [if_pos zero] at normal
      cases normal
    · rw [if_neg zero] at normal
      let entry := decClockHOLFinite source
      have summary := copy_body_local entry
      unfold LocalSummary at summary
      have clock := evaluateHOLFiniteState_clock_le entry copyBody
      generalize bodyRun : evaluateHOLFiniteState entry copyBody = output at normal summary clock
      obtain ⟨result, next⟩ := output
      rw [WitnessRadix.StateSteps.fixed_clock entry next result clock] at normal
      cases result with
      | none =>
        obtain ⟨mapped, present, same⟩ := copy_step_reached entry next pointer (BitVec.ofNat 64 index)
          old pointerLocal indexLocal wordLocal oracleEq bodyRun
        let value := Guest.wordOfLeBytes (SharedRead.bytes entry.ffi.ffiState
          (Guest.inputDataAddr + BitVec.ofNat 64 index))
        have nextP : next.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
          rw [same, wordPost_other entry pointer _ _ (by decide) (by decide)]
          exact pointerLocal
        have nextI : next.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index + 8)))) := by
          rw [same]
          simpa only [BitVec.ofNat_add] using wordPost_index entry pointer (BitVec.ofNat 64 index)
        have nextL : next.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))) := by
          rw [same, wordPost_other entry pointer _ _ (by decide) (by decide)]
          exact lengthLocal
        have nextW : next.locals.lookup (ofString "w") = some (.val (.word value)) := by
          rw [same]
          exact wordPost_word entry pointer _
        have nextOracle : next.ffi.oracle = InitE.sourceOracle := by rw [same]; exact oracleEq
        obtain ⟨tailState, tailObserved⟩ := ih next target value (index + 8) (by omega) (by omega)
          nextP nextI nextL nextW nextOracle normal
        constructor
        · rw [tailState, same]
          rfl
        · intro slot inside
          cases slot with
          | zero =>
            simpa only [Nat.mul_zero, Nat.add_zero, entry, decClockHOLFinite] using And.intro mapped present
          | succ slot =>
            have observed := tailObserved slot (by omega)
            rw [same] at observed
            have arithmetic : index + 8 * (slot + 1) = index + 8 + 8 * slot := by omega
            simpa only [arithmetic, wordPost, SharedRead.post, WitnessRadix.QueryBranch.bind,
              setVarHOLFinite, SharedRead.nextFfi, entry, decClockHOLFinite] using observed
      | some result =>
        cases result with
        | «break» => exact (summary.2.2.1 rfl).elim
        | «continue» => exact (summary.2.2.2 rfl).elim
        | returned value => cases normal
        | error => cases normal
        | timeOut => cases normal
        | exception name value => cases normal
        | finalFfi event => cases normal

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.copy_loop_reached
