import InitECandidate.Solver.WitnessRadix.Copy32Tests
import InitECandidate.Solver.WitnessRadix.BindingLookup
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.WitnessRadix.Copy32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem loop_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (words : Fin 4 → BitVec 64)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word 0#64)))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word 32#64)))
    (view : MemoryBytes.WordView source src words)
    (mapped : ∀ limb : Fin 4, source.memaddrs (dst + BitVec.ofNat 64 (8 * limb.val)))
    (separate : ∀ read write : Fin 4, src + BitVec.ofNat 64 (8 * read.val) ≠ dst + BitVec.ofNat 64 (8 * write.val))
    (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source loop32 = (none, post (decClockHOLFinite source) dst words) := by
  classical
  let entry := decClockHOLFinite source
  let target := post entry dst words
  have view' : MemoryBytes.WordView entry src words := ⟨view.mapped, view.stored⟩
  have bodyRun : evaluateHOLFiniteState (decClockHOLFinite source) wordBody = (none, target) :=
    block_execute entry src dst words srcLocal dstLocal indexLocal view' mapped separate
  have firstTest := condition_read source 0#64 32#64 indexLocal lengthLocal
  have notLower : ¬ (32#64 : BitVec 64) < 32#64 := by decide
  simp only [BitVec.zero_add, if_neg notLower] at firstTest
  have targetIndex : target.locals.lookup (ofString "i") = some (.val (.word 32#64)) :=
    bind_lookup_same _ "i" 32#64
  have targetLength : target.locals.lookup (ofString "n") = some (.val (.word 32#64)) := by
    unfold target post
    rw [bind_lookup_other _ "i" "n" _ (by decide)]
    exact lengthLocal
  have lower : (32#64 : BitVec 64) < 32#64 + 32#64 := by decide
  have lastTest := condition_read target 32#64 32#64 targetIndex targetLength
  simp only [eval, if_pos lower] at lastTest
  have positive : source.clock ≠ 0 := by omega
  rw [loop32_shape, evaluateHOLFiniteState_while_total, firstTest]
  simp only [show (1#64 : BitVec 64) ≠ 0#64 from by decide, ↓reduceIte,
    if_neg positive, bodyRun]
  rw [StateSteps.fixed_clock entry target none (Nat.le_refl _)]
  change evaluateHOLFiniteState target (.while (condition 32#64) wordBody) = _
  rw [evaluateHOLFiniteState_while_total, lastTest]
  simp
  rfl

theorem remaining_loops {F : Type} (source : PanSemStateFiniteExact 64 F)
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word 32#64)))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word 32#64))) :
    evaluateHOLFiniteState source loopWord = (none, source) ∧
    evaluateHOLFiniteState source loopBytes = (none, source) ∧
    evaluateHOLFiniteState source loopTail = (none, source) := by
  classical
  have lower : (32#64 : BitVec 64) < 32#64 + 8#64 := by decide
  have test := condition_read source 32#64 8#64 indexLocal lengthLocal
  simp only [eval, if_pos lower] at test
  rw [other_loop_shapes.1, other_loop_shapes.2.1, other_loop_shapes.2.2]
  have tailTest : @evalHOLFinite 64 F _ source (fun address => Classical.propDecidable (source.memaddrs address))
      (.cmp .lower (localVar "i") (localVar "n")) = some (.val (.word 0#64)) := by
    simp [evalHOLFinite, localVar, evalHOLExact, toExact, indexLocal, lengthLocal,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  refine ⟨?_, ?_, ?_⟩
  · rw [evaluateHOLFiniteState_while_total, test]; simp
  · rw [evaluateHOLFiniteState_while_total, test]; simp
  · rw [evaluateHOLFiniteState_while_total, tailTest]; simp

end InitECandidate.Solver.WitnessRadix.Copy32

#print axioms InitECandidate.Solver.WitnessRadix.Copy32.loop_execute
#print axioms InitECandidate.Solver.WitnessRadix.Copy32.remaining_loops
