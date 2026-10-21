import InitECandidate.Solver.MutableTable.MemeqAnyProgram
import InitECandidate.Solver.Input.WhileActive

namespace InitECandidate.Solver.MutableTable.MemeqAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The literal byte-comparison loop executes at most four eight-byte
blocks. Genuine fallthrough reaches exactly32, even with arbitrary reads. -/
theorem blocks_summary (blocks index : Nat) (extent : index+8*blocks=32)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (iCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word 32#64))) :
    source.clock-(evaluateHOLFiniteState source (.while Memeq32.condition8 MemeqByteRuntime.blockBody)).2.clock≤blocks ∧
    (∀ post,evaluateHOLFiniteState source (.while Memeq32.condition8 MemeqByteRuntime.blockBody)=(none,post) →
      post.locals.lookup (ofString "i")=some (.val (.word 32#64)) ∧ post.locals.lookup (ofString "n")=some (.val (.word 32#64))) := by
  induction blocks generalizing index source with
  | zero =>
    have number : index=32 := by omega
    subst index
    have test:=MemeqByteRuntime.condition8_read source 32 32 (by decide) (by decide) iCell nCell
    have finiteTest : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) Memeq32.condition8=some (.val (.word 0#64)) := by
      simpa only [eval,evalHOLFinite,if_neg (by decide : ¬32+8≤32)] using test
    rw [evaluateHOLFiniteState_while_total,finiteTest]
    simp only [if_neg (by decide : ¬(0#64 : BitVec 64)≠0#64)]
    exact ⟨by change source.clock-source.clock≤0; omega,by intro post normal; cases normal; exact ⟨iCell,nCell⟩⟩
  | succ blocks ih =>
    have bounded : index≤32 := by omega
    have activeIndex : index+8≤32 := by omega
    have test : eval source Memeq32.condition8=some (.val (.word 1#64)) := by
      simpa only [if_pos activeIndex] using MemeqByteRuntime.condition8_read source index 32 (by decide) bounded iCell nCell
    by_cases zero : source.clock=0
    · have finiteTest : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) Memeq32.condition8=some (.val (.word 1#64)) := by simpa only [eval,evalHOLFinite] using test
      rw [evaluateHOLFiniteState_while_total,finiteTest]
      simp only [if_pos (by decide : (1#64 : BitVec 64)≠0#64),if_pos zero]
      exact ⟨by simp [zero],by intro post impossible; cases impossible⟩
    · have guarded : Input.GuardedCounter 8 MemeqByteRuntime.blockBody := guarded_bodies.2.2.1
      have quiet:=guarded.quiet source.code (decClockHOLFinite source) rfl
      have forward:=evaluateHOLFiniteState_clock_le (decClockHOLFinite source) MemeqByteRuntime.blockBody
      generalize computed : evaluateHOLFiniteState (decClockHOLFinite source) MemeqByteRuntime.blockBody=output at quiet forward
      obtain ⟨answer,target⟩ := output
      have actual:=Input.while_active source target Memeq32.condition8 MemeqByteRuntime.blockBody answer test zero computed forward
      rw [actual]
      change target.clock=source.clock-1 at quiet
      cases answer with
      | none =>
        simp only [Input.whileResume]
        have nextEq:=guarded.normal (decClockHOLFinite source) target (BitVec.ofNat 64 index) iCell computed
        have nextWord : BitVec.ofNat 64 index+8#64=BitVec.ofNat 64 (index+8) := by simp [BitVec.ofNat_add]
        have nextI : target.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+8)))) := by
          rw [nextEq,← nextWord]; exact bind_lookup_same _ _ _
        have nextN : target.locals.lookup (ofString "n")=some (.val (.word 32#64)) := by
          rw [nextEq]; exact (bind_lookup_other _ "i" "n" _ (by decide)).trans nCell
        have back:=ih (index+8) (by omega) target nextI nextN
        have remaining:=evaluateHOLFiniteState_clock_le target (.while Memeq32.condition8 MemeqByteRuntime.blockBody)
        exact ⟨by omega,back.2⟩
      | some answer =>
        have controls:=guarded.no_control (decClockHOLFinite source)
        rw [computed] at controls
        cases answer with
        | «break» => exact (controls.1 rfl).elim
        | «continue» => exact (controls.2 rfl).elim
        | _ =>
          simp only [Input.whileResume]
          exact ⟨by omega,by intro post impossible; cases impossible⟩

/-- With an actual initial i=0 and n=32, all byte-tail work costs at most
four source ticks; the final byte loop is skipped on genuine fallthrough. -/
theorem tail_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (iCell : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word 32#64))) :
    source.clock-(evaluateHOLFiniteState source Memeq32.parts.tailCode).2.clock≤4 := by
  have summary:=blocks_summary 4 0 (by decide) source iCell nCell
  rw [Memeq32.tail_shape]
  have cost:=Input.ClockCost.sequence_reached_current source (.while Memeq32.condition8 MemeqByteRuntime.blockBody)
      (.seq (.while Memeq32.condition1 MemeqByteRuntime.byteBody) (.return (.const 1#64))) 4 0 summary.1 (by
    intro middle normal
    obtain ⟨done,nKept⟩ := summary.2 middle normal
    have test:=Memeq32.eval_condition1_done middle done nKept
    have finiteTest : evalHOLFinite middle (h:=fun address=>Classical.propDecidable (middle.memaddrs address)) Memeq32.condition1=some (.val (.word 0#64)) := by simpa only [eval,evalHOLFinite] using test
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_while_total,finiteTest]
    simp only [if_neg (by decide : ¬(0#64 : BitVec 64)≠0#64)]
    exact Input.ClockCost.returned middle.code _ middle rfl)
  exact cost

end InitECandidate.Solver.MutableTable.MemeqAny

#print axioms InitECandidate.Solver.MutableTable.MemeqAny.blocks_summary
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.tail_cost
