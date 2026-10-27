import InitECandidate.Solver.Input.VarList.CountChecks

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def counted (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first : BitVec 64) := bind source "count" (countWord first)

/-- Both real first/count guards, including rejection and lexical restoration.
Passing reaches the actual allocator call without changing memory or clock. -/
theorem first_guards (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first length limit : BitVec 64)
    (f : source.locals.lookup (ofString "first")=some (.val (.word first)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (l : source.locals.lookup (ofString "lim")=some (.val (.word limit)))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source firstTail=
      if badFirst first length then
        (some (.exception (ofString "SszErr") (.val (.word 21#64))),emptyLocalsHOLFinite {source with clock:=source.clock-1})
      else if limit<countWord first then
        (some (.exception (ofString "SszErr") (.val (.word 22#64))),
          restore source "count" (emptyLocalsHOLFinite {counted source first with clock:=source.clock-1}))
      else (let output:=evaluateHOLFiniteState (counted source first) allocationCall;
        (output.1,restore source "count" output.2)) := by
  classical
  have firstRun : evaluateHOLFiniteState source firstGuard=
      if badFirst first length then
        (some (.exception (ofString "SszErr") (.val (.word 21#64))),emptyLocalsHOLFinite {source with clock:=source.clock-1})
      else (none,source) :=
    Header.test_guard_execute source firstTest 21#64 _ (first_test_read source first length f n) failCode exceptionShape enough
  have countRead:=count_read source first f
  have setup : WitnessRadix.BuildEntry.Initializes source [("count", countExpression)] (counted source first) (fun target=>restore source "count" target) :=
    WitnessRadix.BuildEntry.Initializes.step _ countRead (.done _)
  have declarationRun:=WitnessRadix.BuildEntry.declarations_execute setup (.seq countGuard allocationCall)
  have countPresent : (counted source first).locals.lookup (ofString "count")=some (.val (.word (countWord first))) := bind_lookup_same _ _ _
  have limitPresent : (counted source first).locals.lookup (ofString "lim")=some (.val (.word limit)) :=
    (bind_lookup_other source "count" "lim" _ (by decide)).trans l
  have countRun : evaluateHOLFiniteState (counted source first) countGuard=
      if limit<countWord first then
        (some (.exception (ofString "SszErr") (.val (.word 22#64))),emptyLocalsHOLFinite {counted source first with clock:=source.clock-1})
      else (none,counted source first) :=
    Header.test_guard_execute (counted source first) countTest 22#64 _
      (count_test_read (counted source first) (countWord first) limit countPresent limitPresent) failCode exceptionShape enough
  rw [first_tail_shape]
  by_cases bad : badFirst first length
  · simp only [if_pos bad] at firstRun ⊢
    exact WitnessRadix.StateSteps.stopped_sequence source _ firstGuard _ _ firstRun (by change source.clock-1≤source.clock; omega)
  · simp only [if_neg bad] at firstRun ⊢
    rw [WitnessRadix.StateSteps.next_sequence source source firstGuard _ firstRun (Nat.le_refl _)]
    change evaluateHOLFiniteState source (WitnessRadix.BuildEntry.declarations [("count", countExpression)] (.seq countGuard allocationCall))=_
    rw [declarationRun]
    by_cases over : limit<countWord first
    · simp only [if_pos over] at countRun ⊢
      rw [WitnessRadix.StateSteps.stopped_sequence (counted source first) _ countGuard allocationCall _ countRun (by change source.clock-1≤source.clock; omega)]
    · simp only [if_neg over] at countRun ⊢
      rw [WitnessRadix.StateSteps.next_sequence (counted source first) (counted source first) countGuard allocationCall countRun (Nat.le_refl _)]

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.first_guards
