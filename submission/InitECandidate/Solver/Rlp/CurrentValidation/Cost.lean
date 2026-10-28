import InitECandidate.Solver.Rlp.CurrentValidation.Loop
import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Rlp.CurrentValidation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

def seeded (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64) :=
  bind (bind (bind (bind source "top" 0#64) "pos" pointer) "end" (pointer+length)) "go" 1#64

theorem seeded_state (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64) :
    State (seeded source pointer length) pointer (pointer+length) 1#64 := by
  refine ⟨arena.of_frame rfl,?_,?_,?_,?_,?_,Or.inr rfl,?_⟩
  · rw [seeded,bind_lookup_other _ "go" "pos" _ (by decide),bind_lookup_other _ "end" "pos" _ (by decide)]
    exact bind_lookup_same _ _ _
  · rw [seeded,bind_lookup_other _ "go" "end" _ (by decide)]
    exact bind_lookup_same _ _ _
  · rw [seeded,bind_lookup_other _ "go" "top" _ (by decide),bind_lookup_other _ "end" "top" _ (by decide),bind_lookup_other _ "pos" "top" _ (by decide)]
    exact bind_lookup_same _ _ _
  · exact bind_lookup_same _ _ _
  · rw [BitVec.toNat_add_of_lt fits]
    omega
  · intro impossible
    exact False.elim ((by decide : (1#64 : BitVec 64)≠0#64) impossible)

/-- Complete unchanged internal RLP validator under its actual initialized
below-domain scratch state, including all setup declarations and final return.
No mapped scratch frame, successful future parse or allocation room is assumed.
All outcomes spend at most14*(length+1) source call/loop ticks. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64) :
    source.clock-(evaluateHOLFiniteState source Validation.body).2.clock≤14*(length.toNat+1) := by
  let topState:=bind source "top" 0#64
  let positionState:=bind topState "pos" pointer
  let endState:=bind positionState "end" (pointer+length)
  let goState:=bind endState "go" 1#64
  have data : State goState pointer (pointer+length) 1#64 := seeded_state source pointer length arena fits
  have loopPrice : goState.clock-(evaluateHOLFiniteState goState Validation.loop).2.clock≤14*(length.toNat+1) := by
    have paid:=loop_cost goState pointer (pointer+length) 1#64 data
    simpa only [BitVec.toNat_add_of_lt fits,Nat.add_sub_cancel_left,show (1#64 : BitVec 64).toNat=1 from by decide] using paid
  have tail:=ClockCost.sequence_current goState Validation.loop (.return (.const 0#64)) (14*(length.toNat+1)) 0 loopPrice (ClockCost.returned goState.code _)
  simp only [Nat.add_zero] at tail
  have goDecl:=ClockCost.declared_current endState "go" (.const 1#64) 1#64 (.seq Validation.loop (.return (.const 0#64))) (14*(length.toNat+1)) rfl tail
  have currentPointer : positionState.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other topState "pos" "p" pointer (by decide)).trans ((bind_lookup_other source "top" "p" 0#64 (by decide)).trans pointerCell)
  have currentLength : positionState.locals.lookup (ofString "len")=some (.val (.word length)) :=
    (bind_lookup_other topState "pos" "len" pointer (by decide)).trans ((bind_lookup_other source "top" "len" 0#64 (by decide)).trans lengthCell)
  have endRead : eval positionState (.op .add [localVar "p",localVar "len"])=some (.val (.word (pointer+length))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,currentPointer,currentLength,valueIsWord,valueWord,wordOpHOL,wordOp]
  have endDecl:=ClockCost.declared_current positionState "end" _ (pointer+length) _ (14*(length.toNat+1)) endRead goDecl
  have pointerRead : eval topState (localVar "p")=some (.val (.word pointer)) := by
    have current:=(bind_lookup_other source "top" "p" 0#64 (by decide)).trans pointerCell
    change topState.locals.lookup (ofString "p")=_ at current
    simp [eval,evalHOLExact,localVar,toExact,current]
  have positionDecl:=ClockCost.declared_current topState "pos" _ pointer _ (14*(length.toNat+1)) pointerRead endDecl
  rw [Validation.body_shape]
  exact ClockCost.declared_current source "top" (.const 0#64) 0#64 _ (14*(length.toNat+1)) rfl positionDecl

end InitECandidate.Solver.Rlp.CurrentValidation

#print axioms InitECandidate.Solver.Rlp.CurrentValidation.seeded_state
#print axioms InitECandidate.Solver.Rlp.CurrentValidation.body_cost
