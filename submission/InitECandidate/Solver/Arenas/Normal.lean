import InitE.SourceSemantics
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

/-- Every aligned cell inside a successful downward scratch allocation is
mapped in current main. Room is the allocator's checked natural guard; it
also prevents wrapping when the cell address is formed. -/
theorem downward_scratch_cell (pointer limit amount : BitVec 64) (offset : Nat)
    (lower : InitE.scratchStart ≤ limit.toNat) (upper : pointer.toNat ≤ InitE.scratchEnd)
    (aligned : limit.toNat % 8 = 0) (room : Room .down pointer limit amount)
    (inside : offset < amount.toNat) (offsetAligned : offset % 8 = 0) :
    InitE.ordinaryDomain (resultWord .down pointer amount + BitVec.ofNat 64 offset) := by
  have guards := downward_guards pointer limit amount aligned room
  have qLower := guards.2.2.1
  have qUpper := guards.2.2.2.1
  have qAligned := guards.2.2.2.2.2
  have offsetSmall : offset < 2^64 := by have bound := amount.isLt; omega
  have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt offsetSmall]
  have noWrap : (rounded .down pointer amount).toNat + (BitVec.ofNat 64 offset).toNat < 2^64 := by
    rw [offsetNat]
    dsimp [InitE.scratchEnd] at upper
    omega
  have address : (resultWord .down pointer amount + BitVec.ofNat 64 offset).toNat =
      (rounded .down pointer amount).toNat + offset := by
    change (rounded .down pointer amount + BitVec.ofNat 64 offset).toNat = _
    rw [BitVec.toNat_add_of_lt noWrap, offsetNat]
  apply InitE.scratch_in_ordinaryDomain
  · rw [address, Nat.add_mod, qAligned, offsetAligned]
  · rw [address]
    exact ⟨by omega, by omega⟩

/-- A real normal scratch return derives its own room and mapped returned
cells. This replaces the old early-failure argument for current main; no
successful future store or clear is assumed. -/
theorem scratch_cell_of_normal {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (pointer limit amount : BitVec 64) (offset : Nat)
    (amountLocal : source.locals.lookup (ofString "n") = some (.val (.word amount)))
    (pointerGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word limit)))
    (ordered : Ordered .down pointer limit) (aligned : limit.toNat % 8 = 0)
    (lower : InitE.scratchStart ≤ limit.toNat) (upper : pointer.toNat ≤ InitE.scratchEnd)
    (inside : offset < amount.toNat) (offsetAligned : offset % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (trapInstalled : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (body .down) = (some (.returned value), target)) :
    value = .val (.word (resultWord .down pointer amount)) ∧
      target.memaddrs (resultWord .down pointer amount + BitVec.ofNat 64 offset) := by
  obtain ⟨room, returned, frame⟩ := post_of_normal source target .down pointer limit amount
    amountLocal pointerGlobal limitGlobal ordered aligned trapInstalled value normal
  refine ⟨returned, ?_⟩
  have sameDomain := congrArg (fun state : PanSemStateFiniteExact 64 F => state.memaddrs) frame
  change target.memaddrs = source.memaddrs at sameDomain
  rw [sameDomain, domain]
  exact downward_scratch_cell pointer limit amount offset lower upper aligned room inside offsetAligned

end InitECandidate.Solver.Arenas

#print axioms InitECandidate.Solver.Arenas.room_of_normal
#print axioms InitECandidate.Solver.Arenas.post_of_normal

#print axioms InitECandidate.Solver.Arenas.downward_scratch_cell
#print axioms InitECandidate.Solver.Arenas.scratch_cell_of_normal
