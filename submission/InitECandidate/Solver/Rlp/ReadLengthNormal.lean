import InitECandidate.Solver.Rlp.ReadLengthUnique
import InitECandidate.Solver.Rlp.FailGuardReturn
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Rlp.ReadLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def seed (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind (bind source "v" 0#64) "i" 0#64

theorem seed_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length))) :
    Locals (seed source) pointer length 0#64 0#64 := by
  refine ⟨?_,?_,bind_lookup_same _ _ _,?_⟩
  · exact (bind_lookup_other _ "i" "p" _ (by decide)).trans
      ((bind_lookup_other _ "v" "p" _ (by decide)).trans pointerCell)
  · exact (bind_lookup_other _ "i" "n" _ (by decide)).trans
      ((bind_lookup_other _ "v" "n" _ (by decide)).trans lengthCell)
  · exact (bind_lookup_other _ "i" "v" _ (by decide)).trans (bind_lookup_same _ _ _)

/-- Recover the actual initialized reader loop and returned accumulator
from an actual return of the unchanged original function. -/
theorem body_loop (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    ∃ loopPost, evaluateHOLFiniteState (seed source) loop=(none,loopPost) ∧
      loopPost.locals.lookup (ofString "v")=some returned := by
  rw [body_shape] at normal
  obtain ⟨guardRun,afterGuardRun⟩ := Fail.guard_return source post guardTest [.const 2#64] afterGuard returned installed normal
  rw [after_guard_shape] at afterGuardRun
  obtain ⟨valuePost,valueRun,valueRestored⟩ := Input.declaration_return_word source post "v" (.const 0#64) 0#64 _ returned rfl afterGuardRun
  obtain ⟨indexPost,indexRun,indexRestored⟩ := Input.declaration_return_word (bind source "v" 0#64) valuePost "i" (.const 0#64) 0#64 _ returned rfl valueRun
  have safe : Input.LocalPrefix (ofString "n") loop := by rw [loop_shape]; exact .loop condition loop_body_limit
  obtain ⟨loopPost,loopRun,returnRun,locals⟩ := safe.normal_continue (seed source) indexPost (.return (localVar "v")) returned indexRun
  have actual := (Input.return_normal loopPost indexPost (localVar "v") returned returnRun).1
  exact ⟨loopPost,loopRun,by simpa only [eval,evalHOLExact,localVar,toExact] using actual⟩

/-- Actual original length-reader returns are determined by the selected
input bytes, independently of clocks and unrelated state. -/
theorem body_unique (left right leftPost rightPost : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length : BitVec 64) (leftValue rightValue : ValueHOL 64)
    (leftPointer : left.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (leftLength : left.locals.lookup (ofString "n")=some (.val (.word length)))
    (rightPointer : right.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (rightLength : right.locals.lookup (ofString "n")=some (.val (.word length)))
    (bytes : BytesAgree left right pointer length)
    (leftInstalled : Input.OriginalCode.Installed left.code) (rightInstalled : Input.OriginalCode.Installed right.code)
    (leftRun : evaluateHOLFiniteState left body=(some (.returned leftValue),leftPost))
    (rightRun : evaluateHOLFiniteState right body=(some (.returned rightValue),rightPost)) : leftValue=rightValue := by
  obtain ⟨leftLoop,leftLoopRun,leftReturned⟩ := body_loop left leftPost leftValue leftInstalled leftRun
  obtain ⟨rightLoop,rightLoopRun,rightReturned⟩ := body_loop right rightPost rightValue rightInstalled rightRun
  have same := loop_unique (seed left) (seed right) leftLoop rightLoop pointer length 0#64 0#64
    (seed_locals left pointer length leftPointer leftLength) (seed_locals right pointer length rightPointer rightLength)
    bytes leftLoopRun rightLoopRun
  rw [leftReturned,rightReturned] at same
  exact Option.some.inj same

end InitECandidate.Solver.Rlp.ReadLength

#print axioms InitECandidate.Solver.Rlp.ReadLength.seed_locals
#print axioms InitECandidate.Solver.Rlp.ReadLength.body_loop
#print axioms InitECandidate.Solver.Rlp.ReadLength.body_unique
