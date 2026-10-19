import InitECandidate.Solver.Arenas.Calls
import InitECandidate.Solver.PanDeclarations
import InitECandidate.Solver.Input.TrapNoReturn
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Arenas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def Ordered : Direction → BitVec 64 → BitVec 64 → Prop
  | .up, pointer, limit => pointer ≤ limit
  | .down, pointer, limit => limit ≤ pointer

/-- The original allocator's actual normal return rules out its real trap
and derives request room from the current cursor order. No future room or
successful helper execution is supplied. -/
theorem room_of_normal {F : Type} (source target : PanSemStateFiniteExact 64 F) (direction : Direction) (pointer limit amount : BitVec 64)
    (amountLocal : source.locals.lookup (ofString "n") = some (.val (.word amount)))
    (pointerGlobal : source.globals.lookup (ofString (pointerName direction)) = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString (limitName direction)) = some (.val (.word limit)))
    (ordered : Ordered direction pointer limit)
    (trapInstalled : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (body direction) = (some (.returned value), target)) :
    Room direction pointer limit amount := by
  classical
  let entered := WitnessRadix.QueryBranch.bind source "p" pointer
  have pointerRead : eval source (pointerExpression direction) = some (.val (.word pointer)) := by
    simp [eval, pointerExpression, evalHOLExact, toExact, pointerGlobal]
  have setup : WitnessRadix.BuildEntry.Initializes source [("p", pointerExpression direction)] entered (fun output => restore source "p" output) :=
    .step pointer pointerRead (.done _)
  have declared := WitnessRadix.BuildEntry.declarations_execute setup (pTail direction)
  have declaredNormal := normal
  rw [body_shape] at declaredNormal
  have resultEq := congrArg Prod.fst (declared.symm.trans declaredNormal)
  change (evaluateHOLFiniteState entered (pTail direction)).1 = some (.returned value) at resultEq
  have tailRun : evaluateHOLFiniteState entered (pTail direction) = (some (.returned value), (evaluateHOLFiniteState entered (pTail direction)).2) := Prod.ext resultEq rfl
  have safe : Input.LocalPrefix (ofString "n") (firstGuard direction) := .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨middle, firstRun, _, _⟩ := safe.normal_continue entered (evaluateHOLFiniteState entered (pTail direction)).2
    (.dec (ofString "q") .one (roundExpression direction) (qTail direction)) value tailRun
  have pLocal : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := bind_lookup_same _ _ _
  have nLocal : entered.locals.lookup (ofString "n") = some (.val (.word amount)) := (bind_lookup_other _ "p" "n" _ (by decide)).trans amountLocal
  have limitP : entered.globals.lookup (ofString (limitName direction)) = some (.val (.word limit)) := limitGlobal
  have fit : ¬distance direction pointer limit < amount := by
    intro bad
    have chosen : evaluateHOLFiniteState entered (firstGuard direction) = evaluateHOLFiniteState entered (trap direction) := by
      rw [firstGuard, evaluateHOLFiniteState_ite]
      cases direction <;> simp only [distanceExpression, limitExpression, limitName, distance] at bad limitP ⊢ <;>
        simp [evalHOLExact, evalListHOLExact, toExact, localVar, pLocal, nLocal, limitP, valueIsWord, valueWord,
          wordOpHOL, wordOp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bad]
    have actualTrap := chosen.symm.trans firstRun
    have args : evalListHOLFinite entered (h := fun address => Classical.propDecidable (entered.memaddrs address)) [.const (trapCode direction)] =
        some (Input.Trap.values (trapCode direction)) := by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, Input.Trap.values]
    exact Input.Trap.call_not_normal entered middle [.const (trapCode direction)] (trapCode direction) trapInstalled args actualTrap
  cases direction with
  | up =>
    have number := BitVec.toNat_sub_of_le ordered
    change (limit - pointer).toNat = limit.toNat - pointer.toNat at number
    change ¬(limit - pointer).toNat < amount.toNat at fit
    rw [number] at fit
    change pointer.toNat ≤ limit.toNat at ordered
    change pointer.toNat + amount.toNat ≤ limit.toNat
    omega
  | down =>
    have number := BitVec.toNat_sub_of_le ordered
    change (pointer - limit).toNat = pointer.toNat - limit.toNat at number
    change ¬(pointer - limit).toNat < amount.toNat at fit
    rw [number] at fit
    change limit.toNat ≤ pointer.toNat at ordered
    change limit.toNat + amount.toNat ≤ pointer.toNat
    omega

theorem post_of_normal {F : Type} (source target : PanSemStateFiniteExact 64 F) (direction : Direction) (pointer limit amount : BitVec 64)
    (amountLocal : source.locals.lookup (ofString "n") = some (.val (.word amount)))
    (pointerGlobal : source.globals.lookup (ofString (pointerName direction)) = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString (limitName direction)) = some (.val (.word limit)))
    (ordered : Ordered direction pointer limit) (aligned : limit.toNat % 8 = 0)
    (trapInstalled : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (body direction) = (some (.returned value), target)) :
    Room direction pointer limit amount ∧ value = .val (.word (resultWord direction pointer amount)) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite (post source direction pointer amount) := by
  have room := room_of_normal source target direction pointer limit amount amountLocal pointerGlobal limitGlobal ordered trapInstalled value normal
  have guards := room_guards direction pointer limit amount aligned room
  obtain ⟨expected, executed, frame⟩ := execute source direction pointer limit amount amountLocal pointerGlobal limitGlobal guards.1 guards.2
  have same := normal.symm.trans executed
  have result := congrArg Prod.fst same
  have state := congrArg Prod.snd same
  change target = expected at state
  refine ⟨room, ?_, ?_⟩
  · simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using result
  · rw [state]
    exact frame

end InitECandidate.Solver.Arenas

#print axioms InitECandidate.Solver.Arenas.room_of_normal
#print axioms InitECandidate.Solver.Arenas.post_of_normal
