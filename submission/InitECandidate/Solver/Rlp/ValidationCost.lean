import InitECandidate.Solver.Rlp.ValidationLoop
import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def seeded (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64) :=
  bind (bind (bind (bind source "top" 0#64) "pos" pointer) "end" (pointer+length)) "go" 1#64

theorem seeded_view (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (arena : Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64) :
    View (seeded source pointer length) (pointer+length) cursor limit pointer (pointer+length) 1#64 [] := by
  refine ⟨Arena.of_fields source _ cursor limit arena rfl rfl,?_,?_,?_,?_,?_,Or.inr rfl,rfl⟩
  · rw [seeded,bind_lookup_other _ "go" "pos" _ (by decide),bind_lookup_other _ "end" "pos" _ (by decide)]
    exact bind_lookup_same _ _ _
  · rw [seeded,bind_lookup_other _ "go" "end" _ (by decide)]
    exact bind_lookup_same _ _ _
  · rw [seeded,bind_lookup_other _ "go" "top" _ (by decide),bind_lookup_other _ "end" "top" _ (by decide),bind_lookup_other _ "pos" "top" _ (by decide)]
    exact bind_lookup_same _ _ _
  · exact bind_lookup_same _ _ _
  · rw [BitVec.toNat_add_of_lt fits]
    omega

/-- Complete original internal validator body, including its actual setup
and final return. All outcomes cost at most14*(2*length+1) source ticks.
The current ordinary arena is an entry condition; no allocation room,
future stack model, funding, or input-byte values are assumed. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤14*(2*length.toNat+1) := by
  let topState := bind source "top" 0#64
  let positionState := bind topState "pos" pointer
  let endState := bind positionState "end" (pointer+length)
  let goState := bind endState "go" 1#64
  have view : View goState (pointer+length) cursor limit pointer (pointer+length) 1#64 [] := seeded_view source pointer length cursor limit arena fits
  have loopPrice := loop_cost goState (pointer+length) limit installed ⟨cursor,pointer,pointer+length,1#64,[],view⟩
  rw [View.rank_eq _ _ _ _ _ _ _ _ view] at loopPrice
  change goState.clock-(evaluateHOLFiniteState goState loop).2.clock≤14*rank (pointer+length) pointer 0 true at loopPrice
  rw [initial pointer length fits] at loopPrice
  have tail := Input.ClockCost.sequence_current goState loop (.return (.const 0#64)) (14*(2*length.toNat+1)) 0 loopPrice (Input.ClockCost.returned goState.code _)
  simp only [Nat.add_zero] at tail
  have goDecl := Input.ClockCost.declared_current endState "go" (.const 1#64) 1#64 (.seq loop (.return (.const 0#64))) (14*(2*length.toNat+1)) rfl tail
  have currentPointer : positionState.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other _ "pos" "p" _ (by decide)).trans ((bind_lookup_other _ "top" "p" _ (by decide)).trans pointerCell)
  have currentLength : positionState.locals.lookup (ofString "len")=some (.val (.word length)) :=
    (bind_lookup_other _ "pos" "len" _ (by decide)).trans ((bind_lookup_other _ "top" "len" _ (by decide)).trans lengthCell)
  have endRead : eval positionState (.op .add [localVar "p",localVar "len"])=some (.val (.word (pointer+length))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,currentPointer,currentLength,valueIsWord,valueWord,wordOpHOL,wordOp]
  have endDecl := Input.ClockCost.declared_current positionState "end" _ (pointer+length) _ (14*(2*length.toNat+1)) endRead goDecl
  have pointerRead : eval topState (localVar "p")=some (.val (.word pointer)) := by
    have current := (bind_lookup_other source "top" "p" 0#64 (by decide)).trans pointerCell
    change topState.locals.lookup (ofString "p")=_ at current
    simp [eval,evalHOLExact,localVar,toExact,current]
  have positionDecl := Input.ClockCost.declared_current topState "pos" _ pointer _ (14*(2*length.toNat+1)) pointerRead endDecl
  rw [body_shape]
  exact Input.ClockCost.declared_current source "top" (.const 0#64) 0#64 _ (14*(2*length.toNat+1)) rfl positionDecl

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.seeded_view
#print axioms InitECandidate.Solver.Rlp.Validation.body_cost
