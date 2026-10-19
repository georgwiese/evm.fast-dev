import InitECandidate.Solver.Rlp.ListCountCost
import InitECandidate.Solver.Input.LoopInvariant

namespace InitECandidate.Solver.Rlp.ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem loop_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (valid : Invariant pointer length cursor limit source)
    (normal : evaluateHOLFiniteState source loop=(none,target)) : Invariant pointer length cursor limit target := by
  rw [loop_shape] at normal
  apply Input.loop_invariant source.code (ofString "p") condition loopBody loop_body_safe (Invariant pointer length cursor limit) ?_ source target rfl valid normal
  intro current codeEq model word read nonzero positive post bodyRun
  obtain ⟨offset,count,view⟩ := model
  have entryView := View.clock current pointer length cursor limit offset count view (current.clock-1)
  obtain ⟨size,advances,bounded,nextView,number,priced⟩ := loop_body_none (decClockHOLFinite current) post pointer length cursor limit offset count entryView
    (by change Input.OriginalCode.Installed current.code; rw [codeEq]; exact installed) bodyRun
  exact ⟨offset+size,count+1#64,nextView⟩

/-- The original list counter returns an actual scalar count<=input length
and the original bounded arena, derived through every real normal iteration. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ countWord : BitVec 64,value=.val (.word countWord) ∧ countWord.toNat≤length.toNat ∧ Validation.Arena target cursor limit := by
  rw [body_shape] at normal
  obtain ⟨countInner,countRun,countRestore⟩ := Input.declaration_return_word source target "count" (.const 0#64) 0#64 _ value rfl normal
  let counted := bind source "count" 0#64
  obtain ⟨offInner,offRun,offRestore⟩ := Input.declaration_return_word counted countInner "off" (.const 0#64) 0#64 _ value rfl countRun
  have noReturns : ∀ returned,(evaluateHOLFiniteState (seeded source) loop).1≠some (.returned returned) := by
    rw [loop_shape]
    exact ((Input.LocalPrefix.loop condition loop_body_safe).summary_full (seeded source)).2.1
  obtain ⟨middle,loopRun,returnRun⟩ := Input.sequence_returned (seeded source) offInner loop (.return (localVar "count")) value noReturns offRun
  have view := seeded_view source pointer length cursor limit pointerCell lengthCell arena fits
  obtain ⟨nextOffset,nextCount,nextView⟩ := loop_none (seeded source) middle pointer length cursor limit installed ⟨0#64,0#64,view⟩ loopRun
  obtain ⟨read,returned⟩ := Input.return_normal middle offInner (localVar "count") value returnRun
  have countRead : eval middle (localVar "count")=some (.val (.word nextCount)) := by
    simp [eval,evalHOLExact,localVar,toExact,nextView.countCell]
  refine ⟨nextCount,Option.some.inj (read.symm.trans countRead),nextView.counted.trans nextView.bounded,
    Validation.Arena.of_fields middle target cursor limit nextView.arena ?_ ?_⟩
  · rw [countRestore,offRestore,returned]
    rfl
  · rw [countRestore,offRestore,returned]
    rfl

end InitECandidate.Solver.Rlp.ListCount

#print axioms InitECandidate.Solver.Rlp.ListCount.loop_none
#print axioms InitECandidate.Solver.Rlp.ListCount.body_normal
