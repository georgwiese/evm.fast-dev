import InitECandidate.Solver.WitnessRadix.Copy32Loop
import InitECandidate.Solver.WitnessRadix.BuildEmpty

namespace InitECandidate.Solver.WitnessRadix.Copy32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

/-- Entire fixed memcpy function for aligned, separated 32-byte ranges.
Exactly one source-clock unit is consumed; all four words and every other
nonlocal field are exposed in the final state. -/
theorem execute {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (words : Fin 4 → BitVec 64)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word 32#64)))
    (mask : (dst ||| src) &&& 7#64 = 0#64) (view : MemoryBytes.WordView source src words)
    (mapped : ∀ limb : Fin 4, source.memaddrs (dst + BitVec.ofNat 64 (8 * limb.val)))
    (separate : ∀ read write : Fin 4, src + BitVec.ofNat 64 (8 * read.val) ≠ dst + BitVec.ofNat 64 (8 * write.val))
    (enough : 1 ≤ source.clock) :
    ∃ target : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite { source with
        memory := memory source.memory dst words
        clock := source.clock - 1 } := by
  classical
  let initial := bind source "i" 0#64
  let written := post (decClockHOLFinite initial) dst words
  have src' : initial.locals.lookup (ofString "src") = some (.val (.word src)) :=
    (bind_lookup_other source "i" "src" _ (by decide)).trans srcLocal
  have dst' : initial.locals.lookup (ofString "dst") = some (.val (.word dst)) :=
    (bind_lookup_other source "i" "dst" _ (by decide)).trans dstLocal
  have n' : initial.locals.lookup (ofString "n") = some (.val (.word 32#64)) :=
    (bind_lookup_other source "i" "n" _ (by decide)).trans lengthLocal
  have i' : initial.locals.lookup (ofString "i") = some (.val (.word 0#64)) := bind_lookup_same source "i" 0#64
  have view' : MemoryBytes.WordView initial src words := ⟨view.mapped, view.stored⟩
  have loopRun := loop_execute initial src dst words src' dst' i' n' view' mapped separate enough
  have writtenIndex : written.locals.lookup (ofString "i") = some (.val (.word 32#64)) := bind_lookup_same _ "i" 32#64
  have writtenLength : written.locals.lookup (ofString "n") = some (.val (.word 32#64)) := by
    unfold written post
    rw [bind_lookup_other _ "i" "n" _ (by decide)]
    exact n'
  have remaining := remaining_loops written writtenIndex writtenLength
  have clockLe : written.clock ≤ initial.clock := by change source.clock - 1 ≤ source.clock; omega
  have alignedRun : evaluateHOLFiniteState initial (.seq loop32 loopWord) = (none, written) :=
    (StateSteps.next_sequence initial written loop32 loopWord loopRun clockLe).trans remaining.1
  have test := alignment_read initial src dst src' dst' mask
  simp only [eval] at test
  have chosen : evaluateHOLFiniteState initial (.ite alignment (.seq loop32 loopWord) .skip) = (none, written) := by
    rw [evaluateHOLFiniteState_ite, test]
    simpa using alignedRun
  have tailRun : evaluateHOLFiniteState written (.seq loopBytes (.seq loopTail (.return (.const 0#64)))) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite written) := by
    rw [StateSteps.next_sequence written written loopBytes _ remaining.2.1 (Nat.le_refl _),
      StateSteps.next_sequence written written loopTail _ remaining.2.2 (Nat.le_refl _)]
    exact BuildEntry.zero_return written
  have sequence := (StateSteps.next_sequence initial written _ _ chosen clockLe).trans tailRun
  let target := restore source "i" (emptyLocalsHOLFinite written)
  refine ⟨target, ?_, rfl⟩
  rw [body_shape, evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let output := (evaluateHOLFiniteState initial
      (.seq (.ite alignment (.seq loop32 loopWord) .skip)
        (.seq loopBytes (.seq loopTail (.return (.const 0#64))))))
    (output.1, restore source "i" output.2)) = _
  rw [sequence]

end InitECandidate.Solver.WitnessRadix.Copy32

#print axioms InitECandidate.Solver.WitnessRadix.Copy32.execute
