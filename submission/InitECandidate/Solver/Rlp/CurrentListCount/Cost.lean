import InitECandidate.Solver.Rlp.CurrentListCount.Loop
import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Rlp.CurrentListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

def seeded (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind (bind source "count" 0#64) "off" 0#64

theorem seeded_view (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64) : View (seeded source) pointer length 0#64 0#64 := by
  refine ⟨arena.of_frame rfl,?_,?_,?_,?_,Nat.le_refl _,?_,fits⟩
  · exact (bind_lookup_other (bind source "count" 0#64) "off" "p" 0#64 (by decide)).trans ((bind_lookup_other source "count" "p" 0#64 (by decide)).trans pointerCell)
  · exact (bind_lookup_other (bind source "count" 0#64) "off" "len" 0#64 (by decide)).trans ((bind_lookup_other source "count" "len" 0#64 (by decide)).trans lengthCell)
  · exact bind_lookup_same _ _ _
  · exact (bind_lookup_other (bind source "count" 0#64) "off" "count" 0#64 (by decide)).trans (bind_lookup_same _ _ _)
  · change 0≤length.toNat
    exact Nat.zero_le _

/-- Complete unchanged list-count body. Each real item pays from its consumed
bytes, so all outcomes fit60*length source ticks. Both initial declarations
and the final returned count are included, with the actual mapped scratch arena. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64) :
    source.clock-(evaluateHOLFiniteState source ListCount.body).2.clock≤60*length.toNat := by
  let counted:=bind source "count" 0#64
  let entered:=seeded source
  have view:=seeded_view source pointer length pointerCell lengthCell arena fits
  have paid:=loop_cost entered pointer length ⟨0#64,0#64,view⟩
  rw [view.allowance_eq] at paid
  simp only [show (0#64 : BitVec 64).toNat=0 from by decide,Nat.sub_zero] at paid
  have tail:=ClockCost.sequence_current entered ListCount.loop (.return (localVar "count")) (60*length.toNat) 0 paid (ClockCost.returned source.code _)
  simp only [Nat.add_zero] at tail
  have offDecl:=ClockCost.declared_current counted "off" (.const 0#64) 0#64 (.seq ListCount.loop (.return (localVar "count"))) (60*length.toNat) rfl tail
  rw [ListCount.body_shape]
  exact ClockCost.declared_current source "count" (.const 0#64) 0#64 _ (60*length.toNat) rfl offDecl

end InitECandidate.Solver.Rlp.CurrentListCount

#print axioms InitECandidate.Solver.Rlp.CurrentListCount.seeded_view
#print axioms InitECandidate.Solver.Rlp.CurrentListCount.body_cost
