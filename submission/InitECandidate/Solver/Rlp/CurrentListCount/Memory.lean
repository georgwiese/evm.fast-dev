import InitECandidate.Solver.Rlp.CurrentListCount.Cost
import InitECandidate.Solver.Input.LoopInvariant
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Rlp.CurrentListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

theorem loop_none_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length offset count : BitVec 64)
    (view : View source pointer length offset count) (normal : evaluateHOLFiniteState source ListCount.loop=(none,post)) :
    Invariant pointer length post ∧ LocalEffects.erase post=LocalEffects.erase source := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>Invariant pointer length current ∧ LocalEffects.erase current=LocalEffects.erase source
  have initial : invariant source := ⟨⟨offset,count,view⟩,rfl⟩
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) ListCount.condition=some (.val (.word word)) →
      word≠0 → current.clock≠0 → ∀ target,evaluateHOLFiniteState (decClockHOLFinite current) ListCount.loopBody=(none,target) → invariant target := by
    intro current codeEq model word read nonzero funded target actual
    obtain ⟨offset,count,view⟩ := model.1
    obtain ⟨size,positive,bounded,nextView,number,price,frame⟩ := loop_body_none (decClockHOLFinite current) target pointer length offset count (view.at_clock (current.clock-1)) actual
    exact ⟨⟨offset+size,count+1#64,nextView⟩,frame.trans model.2⟩
  rw [ListCount.loop_shape] at normal
  exact loop_invariant source.code (ofString "p") ListCount.condition ListCount.loopBody loop_body_safe invariant progress source post rfl initial normal

/-- A real normal list count returns an actual word bounded by the original
byte length and preserves all nonlocal state, through both declarations, every
real parsed item, the exact increments, return and lexical restoration. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source ListCount.body=(some (.returned value),post)) :
    ∃ count : BitVec 64,value=.val (.word count) ∧ count.toNat≤length.toNat ∧ LocalEffects.erase post=LocalEffects.erase source := by
  rw [ListCount.body_shape] at normal
  obtain ⟨countInner,countRun,countRestore⟩ := declaration_return_word source post "count" (.const 0#64) 0#64 _ value rfl normal
  let counted:=bind source "count" 0#64
  obtain ⟨offInner,offRun,offRestore⟩ := declaration_return_word counted countInner "off" (.const 0#64) 0#64 _ value rfl countRun
  let entered:=seeded source
  have noReturns : ∀ returned,(evaluateHOLFiniteState entered ListCount.loop).1≠some (.returned returned) := by
    rw [ListCount.loop_shape]
    exact ((LocalPrefix.loop ListCount.condition loop_body_safe).summary_full entered).2.1
  obtain ⟨middle,loopRun,returnRun⟩ := sequence_returned entered offInner ListCount.loop (.return (localVar "count")) value noReturns offRun
  obtain ⟨model,frame⟩ := loop_none_frame entered middle pointer length 0#64 0#64 (seeded_view source pointer length pointerCell lengthCell arena fits) loopRun
  obtain ⟨offset,count,view⟩ := model
  obtain ⟨read,returned⟩ := return_normal middle offInner (localVar "count") value returnRun
  have actualCount : eval middle (localVar "count")=some (.val (.word count)) := by
    simp [eval,evalHOLExact,localVar,toExact,view.countCell]
  refine ⟨count,Option.some.inj (read.symm.trans actualCount),Nat.le_trans view.counted view.bounded,?_⟩
  rw [countRestore,offRestore,returned]
  exact frame

end InitECandidate.Solver.Rlp.CurrentListCount

#print axioms InitECandidate.Solver.Rlp.CurrentListCount.loop_none_frame
#print axioms InitECandidate.Solver.Rlp.CurrentListCount.body_normal
