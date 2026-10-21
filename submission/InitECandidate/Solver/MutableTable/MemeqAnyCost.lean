import InitECandidate.Solver.MutableTable.MemeqAnyProgram
import InitECandidate.Solver.Input.ClockCostCurrent
import InitECandidate.Solver.Input.LocalEffectsLoop

namespace InitECandidate.Solver.MutableTable.MemeqAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem other_model : Model Memeq32.parts.otherAligned 64 := by
  rw [other_shape]
  exact (Model.decision decisions.2.2).sequence
    ((Model.loop (blockTest 32) word32Body 32 (by decide) guarded_bodies.1 (block_test_reads 32 (by decide))).sequence
      (Model.loop (blockTest 8) word8Body 8 (by decide) guarded_bodies.2.1 (block_test_reads 8 (by decide))))

theorem tail_model : Model Memeq32.parts.tailCode 64 := by
  rw [Memeq32.tail_shape]
  exact (Model.loop Memeq32.condition8 Memeq32.byteBodies.1 8 (by decide) guarded_bodies.2.2.1 (block_test_reads 8 (by decide))).sequence
    ((Model.loop Memeq32.condition1 Memeq32.byteBodies.2 1 (by decide) guarded_bodies.2.2.2 byte_test_reads).sequence
      (Model.decision (.returned (.const 1#64))))

/-- A uniform original32-byte comparison bound, including unmapped or
nonword operand reads. Each of the four literal counter loops is at most32
source ticks; the guard/decision work consumes no source call/loop ticks. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word 32#64))) :
    source.clock-(evaluateHOLFiniteState source Memeq32.body).2.clock≤128 := by
  have skipModel : Model .skip 0 := Model.decision .skip
  have twenty:=Model.conditional (Memeq32.sizeTest 20#64) (Model.decision decisions.1) skipModel
  have thirtyTwo:=Model.conditional (Memeq32.sizeTest 32#64) (Model.decision decisions.2.1) skipModel
  have phase:=Model.conditional Memeq32.alignmentTest (twenty.sequence (thirtyTwo.sequence other_model)) skipModel
  have inside:=phase.sequence tail_model
  rw [Memeq32.body_shape]
  let entered:=bind source "i" 0#64
  have valid : Invariant entered := ⟨0#64,bind_lookup_same source "i" 0#64,
    (bind_lookup_other source "i" "n" 0#64 (by decide)).trans lengthCell,by decide⟩
  exact Input.ClockCost.declared_current source "i" (.const 0#64) 0#64 _ 128 rfl (inside.cost entered valid)

set_option maxRecDepth 100000 in
theorem readonly (code) : Input.LocalEffects.Preserves code Memeq32.body := by
  simp only [Memeq32.body,Guest.guestFn_memeq,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | apply Input.LocalEffects.declared
    | apply Input.LocalEffects.sequence
    | apply Input.LocalEffects.conditional
    | apply Input.LocalEffects.loop
    | exact Input.LocalEffects.assign code _ _
    | exact Input.LocalEffects.returned code _
    | exact Input.LocalEffects.skip code

end InitECandidate.Solver.MutableTable.MemeqAny

#print axioms InitECandidate.Solver.MutableTable.MemeqAny.other_model
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.tail_model
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.body_cost
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.readonly
