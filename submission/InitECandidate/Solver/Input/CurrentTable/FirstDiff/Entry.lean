import InitECandidate.Solver.Input.CurrentTable.FirstDiff.ByteLoop
import InitECandidate.Solver.Input.CurrentTable.FirstDiff.Cost

namespace InitECandidate.Solver.Input.CurrentTable.FirstDiff
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual full source return: the least differing bit, or marker256 for
identical keys. Earlier bytes, tested digits and return value come from
this same execution; no independent completed scan is a premise. -/
theorem body_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (a b : BitVec 64) (left right : KeyBits.Key)
    (aCell : source.locals.lookup (ofString "a") = some (.val (.word a)))
    (bCell : source.locals.lookup (ofString "b") = some (.val (.word b)))
    (lengthCell : source.locals.lookup (ofString "key_len") = some (.val (.word 32#64)))
    (aView : ByteView source a left) (bView : ByteView source b right)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value),post)) :
    Answer left right value ∧ LocalEffects.erase post = LocalEffects.erase source := by
  have frame := readonly source.code source rfl
  rw [normal] at frame
  refine ⟨?_,frame⟩
  rw [shapes.1] at normal
  obtain ⟨inner,run,endpoint⟩ := declaration_return_word source post "i" (.const 0#64) 0#64 afterI value
    (by simp [eval,evalHOLExact]) normal
  let entry := bind source "i" 0#64
  have initial : Scan source entry a b left right 0 := by
    refine ⟨rfl,?_,?_,?_,bind_lookup_same _ _ _,?_⟩
    · exact (bind_lookup_other source "i" "a" 0#64 (by decide)).trans aCell
    · exact (bind_lookup_other source "i" "b" 0#64 (by decide)).trans bCell
    · exact (bind_lookup_other source "i" "key_len" 0#64 (by decide)).trans lengthCell
    · intro prior before
      omega
  have ready : ScanInvariant source a b left right entry := ⟨0,by decide,initial⟩
  have afterReturns : ReturnFacts.Returns entry afterI (Answer left right) := by
    rw [shapes.2.1]
    apply ReturnFacts.sequence
    · intro target returned actual
      exact loop_returned source entry target a b left right ready aView bView returned actual
    · intro middle completed
      obtain ⟨state,equal⟩ := loop_none_equal source entry middle a b left right ready aView bView completed
      apply ReturnFacts.returned middle _ (.val (.word 256#64)) (Answer left right)
      · simp [eval,evalHOLExact,evalListHOLExact,localVar,state.lengthCell,valueIsWord,valueWord,panOpHOL]
      · refine ⟨256,by decide,rfl,⟨by decide,?_,by omega⟩⟩
        intro prior inside
        rw [equal]
  exact afterReturns inner value run

theorem body_first (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (a b : BitVec 64) (left right : KeyBits.Key)
    (aCell : source.locals.lookup (ofString "a") = some (.val (.word a)))
    (bCell : source.locals.lookup (ofString "b") = some (.val (.word b)))
    (lengthCell : source.locals.lookup (ofString "key_len") = some (.val (.word 32#64)))
    (aView : ByteView source a left) (bView : ByteView source b right)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value),post)) :
    value = .val (.word (BitVec.ofNat 64 (KeyBits.first left right))) ∧
      LocalEffects.erase post = LocalEffects.erase source := by
  obtain ⟨⟨position,bounded,answer,first⟩,frame⟩ := body_returned source post a b left right aCell bCell lengthCell aView bView value normal
  have unique := first.unique (KeyBits.first_spec left right)
  exact ⟨by simpa only [unique] using answer,frame⟩

end InitECandidate.Solver.Input.CurrentTable.FirstDiff

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.body_returned
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.body_first
