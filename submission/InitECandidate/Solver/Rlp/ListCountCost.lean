import InitECandidate.Solver.Rlp.ListCountLoop

namespace InitECandidate.Solver.Rlp.ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def seeded (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind (bind source "count" 0#64) "off" 0#64

theorem seeded_view (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64) :
    View (seeded source) pointer length cursor limit 0#64 0#64 := by
  refine ⟨Validation.Arena.of_fields source _ cursor limit arena rfl rfl,?_,?_,bind_lookup_same _ _ _,?_,Nat.le_refl _,Nat.zero_le _,fits⟩
  · rw [seeded,bind_lookup_other _ "off" "p" _ (by decide),bind_lookup_other _ "count" "p" _ (by decide)]
    exact pointerCell
  · rw [seeded,bind_lookup_other _ "off" "len" _ (by decide),bind_lookup_other _ "count" "len" _ (by decide)]
    exact lengthCell
  · rw [seeded,bind_lookup_other _ "off" "count" _ (by decide)]
    exact bind_lookup_same _ _ _

/-- Complete unchanged original rlp_list_count body, including actual
initialization and final return, with nested validation already priced. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤60*length.toNat+31 := by
  have view := seeded_view source pointer length cursor limit pointerCell lengthCell arena fits
  have priced := loop_cost (seeded source) pointer length cursor limit installed ⟨0#64,0#64,view⟩
  rw [allowance_eq _ length 0#64 view.offsetCell] at priced
  change (seeded source).clock-(evaluateHOLFiniteState (seeded source) loop).2.clock≤60*(length.toNat-0)+31 at priced
  rw [Nat.sub_zero] at priced
  have tail := Input.ClockCost.sequence_current (seeded source) loop (.return (localVar "count")) (60*length.toNat+31) 0 priced (Input.ClockCost.returned source.code _)
  let counted := bind source "count" 0#64
  have offDecl := Input.ClockCost.declared_current counted "off" (.const 0#64) 0#64 _ (60*length.toNat+31) rfl tail
  rw [body_shape]
  exact Input.ClockCost.declared_current source "count" (.const 0#64) 0#64 _ (60*length.toNat+31) rfl offDecl

end InitECandidate.Solver.Rlp.ListCount

#print axioms InitECandidate.Solver.Rlp.ListCount.seeded_view
#print axioms InitECandidate.Solver.Rlp.ListCount.body_cost
