import InitECandidate.Solver.Input.Requests.CountProgram
import InitECandidate.Solver.Input.FixedList.Environment

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

structure CountLocals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : Nat → BitVec 64) (total pointer cursor : BitVec 64) : Prop where
  offsets : ∀ index < 5,source.locals.lookup (ofString (offsetName index)) = some (.val (.word (words index)))
  length : source.locals.lookup (ofString "len") = some (.val (.word total))
  pointer : source.locals.lookup (ofString "p") = some (.val (.word pointer))
  cursor : source.locals.lookup (ofString "rq") = some (.val (.word cursor))

def countSpan (words : Nat → BitVec 64) (total : BitVec 64) (index : Nat) :=
  (if index + 1 < 5 then words (index+1) else total) - words index

private theorem count_other_names (index : Nat) :
    ofString (countName index) ≠ ofString "len" ∧ ofString (countName index) ≠ ofString "p" ∧ ofString (countName index) ≠ ofString "rq" ∧
    ∀ position,ofString (countName index) ≠ ofString (offsetName position) := by
  cases index with
  | zero =>
    simp only [countName]
    refine ⟨by decide,by decide,by decide,?_⟩
    intro position
    cases position with
    | zero => decide
    | succ position => cases position with
      | zero => decide
      | succ position => cases position with
        | zero => decide
        | succ position => cases position <;> simp only [offsetName] <;> decide
  | succ index =>
    cases index with
    | zero =>
      simp only [countName]
      refine ⟨by decide,by decide,by decide,?_⟩
      intro position
      cases position with
      | zero => decide
      | succ position => cases position with
        | zero => decide
        | succ position => cases position with
          | zero => decide
          | succ position => cases position <;> simp only [offsetName] <;> decide
    | succ index =>
      cases index with
      | zero =>
        simp only [countName]
        refine ⟨by decide,by decide,by decide,?_⟩
        intro position
        cases position with
        | zero => decide
        | succ position => cases position with
          | zero => decide
          | succ position => cases position with
            | zero => decide
            | succ position => cases position <;> simp only [offsetName] <;> decide
      | succ index =>
        cases index with
        | zero =>
          simp only [countName]
          refine ⟨by decide,by decide,by decide,?_⟩
          intro position
          cases position with
          | zero => decide
          | succ position => cases position with
            | zero => decide
            | succ position => cases position with
              | zero => decide
              | succ position => cases position <;> simp only [offsetName] <;> decide
        | succ index =>
          simp only [countName]
          refine ⟨by decide,by decide,by decide,?_⟩
          intro position
          cases position with
          | zero => decide
          | succ position => cases position with
            | zero => decide
            | succ position => cases position with
              | zero => decide
              | succ position => cases position <;> simp only [offsetName] <;> decide

theorem CountLocals.arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : Nat → BitVec 64) (total pointer cursor : BitVec 64)
    (valid : CountLocals source words total pointer cursor) (index : Nat) (small : index < 5) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) (countArguments index) =
      some (FixedList.values (countSpan words total index) (elementSize index) 9223372036854775807#64) := by
  have current := valid.offsets index small
  by_cases more : index+1 < 5
  · have next := valid.offsets (index+1) more
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,countArguments,countSpan,FixedList.values,localVar,more,current,next,valueIsWord,valueWord,wordOpHOL,wordOp]
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,countArguments,countSpan,FixedList.values,localVar,more,current,valid.length,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem CountLocals.after_call (source next : PanSemStateFiniteExact 64 Guest.HostMemory) (words : Nat → BitVec 64) (total pointer cursor count : BitVec 64)
    (valid : CountLocals source words total pointer cursor) (index : Nat)
    (locals : next.locals = source.locals.update (ofString (countName index),.val (.word count))) :
    CountLocals next words total pointer cursor := by
  have names := count_other_names index
  have other (key : MlS) (different : ofString (countName index) ≠ key) : next.locals.lookup key = source.locals.lookup key := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,different]
  exact ⟨fun position small => (other _ (names.2.2.2 position)).trans (valid.offsets position small),
    (other _ names.1).trans valid.length,(other _ names.2.1).trans valid.pointer,(other _ names.2.2.1).trans valid.cursor⟩

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.CountLocals.arguments
#print axioms InitECandidate.Solver.Input.Requests.CountLocals.after_call
