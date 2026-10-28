import InitECandidate.Solver.Headers.DecodeCountTrace
import InitECandidate.Solver.Rlp.SlicesAfterAllocNormal

namespace InitECandidate.Solver.Headers.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def declared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array count : BitVec 64) :=
  bind (bind (bind source "arr" array) "n" count) "is_current" 0#64

def restoreDeclared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array count : BitVec 64)
    (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "arr" (restore (bind source "arr" array) "n" (restore (bind (bind source "arr" array) "n" count) "is_current" target))

/-- Enter the three original lexical declarations from the real slice pair,
retaining all three actual outer restorations on every outcome. -/
theorem list_declarations (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array count : BitVec 64)
    (listCell : source.locals.lookup (ofString "lst")=some (Rlp.Slices.result array count)) :
    evaluateHOLFiniteState source afterList=
      (let output:=evaluateHOLFiniteState (declared source array count) afterCurrent;
       (output.1,restoreDeclared source array count output.2)) := by
  have arrayRead : eval source (.rfield 0 (localVar "lst"))=some (.val (.word array)) := by
    simp [eval,evalHOLExact,localVar,toExact,listCell,Rlp.Slices.result]
  have currentList : (bind source "arr" array).locals.lookup (ofString "lst")=some (Rlp.Slices.result array count) :=
    (bind_lookup_other _ "arr" "lst" _ (by decide)).trans listCell
  have countRead : eval (bind source "arr" array) (.rfield 1 (localVar "lst"))=some (.val (.word count)) := by
    simp [eval,evalHOLExact,localVar,toExact,currentList,Rlp.Slices.result]
  have setup : BuildEntry.Initializes source localDeclarations (declared source array count) (restoreDeclared source array count) :=
    .step array arrayRead (.step count countRead (.step 0#64 rfl (.done _)))
  rw [list_scope_shape]
  exact BuildEntry.declarations_execute setup afterCurrent

theorem declared_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array count : BitVec 64) :
    (declared source array count).locals.lookup (ofString "arr")=some (.val (.word array)) ∧
    (declared source array count).locals.lookup (ofString "n")=some (.val (.word count)) ∧
    (declared source array count).locals.lookup (ofString "is_current")=some (.val (.word 0#64)) := by
  refine ⟨?_,?_,bind_lookup_same _ _ _⟩
  · exact (bind_lookup_other _ "is_current" "arr" _ (by decide)).trans
      ((bind_lookup_other _ "n" "arr" _ (by decide)).trans (bind_lookup_same _ _ _))
  · exact (bind_lookup_other _ "is_current" "n" _ (by decide)).trans (bind_lookup_same _ _ _)

theorem counted_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array count : BitVec 64) :
    (counted (declared source array count) count).locals.lookup (ofString "arr")=some (.val (.word array)) ∧
    (counted (declared source array count) count).locals.lookup (ofString "n")=some (.val (.word count)) ∧
    (counted (declared source array count) count).locals.lookup (ofString "is_current")=some (.val (.word (if count=23#64 then 1#64 else 0#64))) := by
  have cells := declared_cells source array count
  by_cases current : count=23#64
  · simp only [counted,if_pos current]
    exact ⟨(bind_lookup_other _ "is_current" "arr" _ (by decide)).trans cells.1,
      (bind_lookup_other _ "is_current" "n" _ (by decide)).trans cells.2.1,bind_lookup_same _ _ _⟩
  · simpa only [counted,if_neg current] using cells

theorem counted_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array count : BitVec 64) :
    Input.LocalEffects.erase (counted (declared source array count) count)=Input.LocalEffects.erase source ∧
      (counted (declared source array count) count).clock=source.clock := by
  by_cases current : count=23#64
  · simp only [counted,if_pos current]
    exact ⟨rfl,rfl⟩
  · simp only [counted,if_neg current]
    exact ⟨rfl,rfl⟩

/-- Every original header field-count scope either stops without spending a
source tick or reaches the real allocation with a count of21 or23. -/
theorem list_count_trace_any (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (array count : BitVec 64)
    (listCell : source.locals.lookup (ofString "lst")=some (Rlp.Slices.result array count))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterList=(result,post)) :
    source.clock-post.clock≤0 ∨ (count=21#64 ∨ count=23#64) ∧ ∃ inner,
      evaluateHOLFiniteState (counted (declared source array count) count) afterCount=(result,inner) ∧
      post=restoreDeclared source array count inner := by
  rw [list_declarations source array count listCell] at run
  let middle := (evaluateHOLFiniteState (declared source array count) afterCurrent).2
  have actualResult := congrArg Prod.fst run
  have actual : evaluateHOLFiniteState (declared source array count) afterCurrent=(result,middle) := Prod.ext actualResult rfl
  have endpoint : post=restoreDeclared source array count middle := (congrArg Prod.snd run).symm
  have cells := declared_cells source array count
  rcases count_trace_any (declared source array count) middle count cells.2.1 cells.2.2 result actual with stopped|reached
  · have finalClock : post.clock=middle.clock := by rw [endpoint]; rfl
    change source.clock-middle.clock≤0 at stopped
    exact Or.inl (by omega)
  · exact Or.inr ⟨reached.1,middle,reached.2,endpoint⟩

theorem list_count_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (array count : BitVec 64)
    (listCell : source.locals.lookup (ofString "lst")=some (Rlp.Slices.result array count))
    (shape : source.eshapes.lookup (ofString "HdrErr")=some .one)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterList=(result,post)) :
    source.clock-post.clock≤0 ∨ (count=21#64 ∨ count=23#64) ∧ ∃ inner,
      evaluateHOLFiniteState (counted (declared source array count) count) afterCount=(result,inner) ∧
      post=restoreDeclared source array count inner :=
  list_count_trace_any source post array count listCell result run

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.list_declarations
#print axioms InitECandidate.Solver.Headers.Decode.declared_cells
#print axioms InitECandidate.Solver.Headers.Decode.counted_cells
#print axioms InitECandidate.Solver.Headers.Decode.counted_frame
#print axioms InitECandidate.Solver.Headers.Decode.list_count_trace

#print axioms InitECandidate.Solver.Headers.Decode.list_count_trace_any
