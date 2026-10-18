import InitECandidate.Solver.GasBudget.JournalSnapshot
import InitECandidate.Solver.MutableTable.GetNormalCall
import InitECandidate.Solver.Input.TrapNoReturn

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

def limitCondition : ExpHOL 64 := .cmp .notLower countVar (.var .global (ofString "journal_cap"))
def guard (code : BitVec 64) : ProgHOL 64 := .ite limitCondition
  (.call (some (none, none)) (ofString "trap_with") [.const code]) .skip
def setBody : ProgHOL 64 := match Guest.guestFn_jset with | .function fn => progToHOL fn.body | _ => .skip
def deleteBody : ProgHOL 64 := match Guest.guestFn_jdel with | .function fn => progToHOL fn.body | _ => .skip
def setAfterGet : ProgHOL 64 := match setBody with | .decCall _ _ _ _ rest => rest | _ => .skip
def setAfterGuard : ProgHOL 64 := match setAfterGet with | .seq _ rest => rest | _ => .skip
def deleteAfterGet : ProgHOL 64 := match deleteBody with | .decCall _ _ _ _ rest => rest | _ => .skip
def deleteAfterEmpty : ProgHOL 64 := match deleteAfterGet with | .seq _ rest => rest | _ => .skip
def deleteAfterGuard : ProgHOL 64 := match deleteAfterEmpty with | .seq _ rest => rest | _ => .skip
def emptyCondition : ExpHOL 64 := .cmp .equal (.rfield 0 (localVar "old")) (.const 0#64)
def emptyCheck : ProgHOL 64 := .ite emptyCondition (.return (.const 0#64)) .skip

theorem set_shape : setBody = .decCall (ofString "old") Get.pairShape (ofString "htab_get") [localVar "t", localVar "key"]
    (.seq (guard 4#64) setAfterGuard) := by
  simp only [setBody, setAfterGuard, setAfterGet, Guest.guestFn_jset, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, guard, limitCondition, countVar, localVar, Get.pairShape]

theorem delete_shape : deleteBody = .decCall (ofString "old") Get.pairShape (ofString "htab_get") [localVar "t", localVar "key"]
    (.seq emptyCheck (.seq (guard 5#64) deleteAfterGuard)) := by
  simp only [deleteBody, deleteAfterGuard, deleteAfterEmpty, deleteAfterGet, Guest.guestFn_jdel, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, guard, limitCondition, countVar, localVar, Get.pairShape, emptyCheck, emptyCondition]

theorem guard_safe (code : BitVec 64) : Input.LocalPrefix (ofString "old") (guard code) :=
  .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip

theorem limit_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count cap : BitVec 64)
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word cap))) :
    eval source limitCondition = some (.val (.word (if count.toNat < cap.toNat then 0#64 else 1#64))) := by
  by_cases bounded : count.toNat < cap.toNat <;>
    simp [eval, limitCondition, countVar, evalHOLExact, toExact, counter, capacity,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, bounded]

/-- Actual normal continuation rules out the original overflow trap, without
assuming a pure trap or excluding its FFI effects on failing executions. -/
theorem guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (count cap code : BitVec 64)
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word cap)))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.seq (guard code) continuation) = (some (.returned returned), post)) :
    count.toNat < cap.toNat ∧ evaluateHOLFiniteState source continuation = (some (.returned returned), post) := by
  obtain ⟨middle, guardRun, tailRun, saved⟩ := (guard_safe code).normal_continue source post continuation returned normal
  have test := limit_read source count cap counter capacity
  simp only [eval] at test
  by_cases bounded : count.toNat < cap.toNat
  · rw [if_pos bounded] at test
    have actual : evaluateHOLFiniteState source (guard code) = (none, source) := by
      rw [guard, evaluateHOLFiniteState_ite, test]
      simp [evaluateHOLFiniteState_skip]
    have same := congrArg Prod.snd (guardRun.symm.trans actual)
    change middle = source at same
    subst middle
    exact ⟨bounded, tailRun⟩
  · rw [if_neg bounded] at test
    rw [guard, evaluateHOLFiniteState_ite, test] at guardRun
    simp only [ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte] at guardRun
    exact False.elim (Input.Trap.call_not_normal source middle [.const code] code trapCode (by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, Input.Trap.values]) guardRun)

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.set_shape
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.delete_shape
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.limit_read
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.guard_normal
