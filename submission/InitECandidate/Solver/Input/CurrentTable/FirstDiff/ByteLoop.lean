import InitECandidate.Solver.Input.CurrentTable.FirstDiff.ByteLoopState

namespace InitECandidate.Solver.Input.CurrentTable.FirstDiff
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def Answer (left right : KeyBits.Key) (value : ValueHOL 64) : Prop :=
  ∃ position : Nat,position ≤ 256 ∧ value = .val (.word (BitVec.ofNat 64 position)) ∧ KeyBits.First left right position

theorem scan_active {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {a b : BitVec 64} {left right : KeyBits.Key} {index : Nat}
    (ready : Scan origin source a b left right index) (bounded : index ≤ 32) (observed : BitVec 64)
    (actual : evalHOLFinite source (h:=fun query => Classical.propDecidable (source.memaddrs query)) test = some (.val (.word observed)))
    (nonzero : observed ≠ 0#64) : index < 32 := by
  have read := scan_test_read ready bounded
  by_contra inactive
  rw [if_neg inactive] at read
  have same : observed = 0#64 := by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actual.symm.trans read
  exact nonzero same

/-- The real returning byte step yields the first differing Patricia bit. -/
theorem scan_step_returned {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {a b : BitVec 64} {left right : KeyBits.Key} {index : Nat}
    (ready : Scan origin source a b left right index) (inside : index < 32)
    (aView : ByteView origin a left) (bView : ByteView origin b right)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source step = (some (.returned value),post)) : Answer left right value := by
  let byte := left ⟨index,inside⟩ ^^^ right ⟨index,inside⟩
  have read : eval source readX = some (.val (.word (byte.setWidth 64))) := ready.read inside aView bView
  rw [shapes.2.2.2.1] at normal
  obtain ⟨inner,run,endpoint⟩ := declaration_return_word source post "x" readX (byte.setWidth 64) afterX value read normal
  have xCell := bind_lookup_same source "x" (byte.setWidth 64)
  have iCell := (bind_lookup_other source "x" "i" (byte.setWidth 64) (by decide)).trans ready.indexCell
  have front : ReturnFacts.Returns (bind source "x" (byte.setWidth 64)) choice (Answer left right) := by
    rw [shapes.2.2.2.2.2.1]
    apply ReturnFacts.conditional
    · intro target returned actual
      have bitAnswer := different_returned _ target byte (BitVec.ofNat 64 index) xCell iCell returned actual
      obtain ⟨position,bounded,answer,first⟩ := byte_answer left right ⟨index,inside⟩ ready.earlier returned bitAnswer
      exact ⟨position,by omega,answer,first⟩
    · exact ReturnFacts.skip _ _
  have bodyReturns : ReturnFacts.Returns (bind source "x" (byte.setWidth 64)) afterX (Answer left right) := by
    rw [shapes.2.2.2.2.1]
    apply ReturnFacts.sequence _ _ _ _ front
    intro middle continued target returned actual
    have safe : LocalPrefix (ofString "x") (increment "i") := .assign _ _ (by decide)
    exact ((safe.summary_full middle).2.1 returned (congrArg Prod.fst actual)).elim
  exact bodyReturns inner value run

def ScanInvariant (origin : PanSemStateFiniteExact 64 Guest.HostMemory)
    (a b : BitVec 64) (left right : KeyBits.Key) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ index : Nat,index ≤ 32 ∧ Scan origin source a b left right index

theorem scan_progress {origin current target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {a b : BitVec 64} {left right : KeyBits.Key}
    (ready : ScanInvariant origin a b left right current)
    (aView : ByteView origin a left) (bView : ByteView origin b right) (observed : BitVec 64)
    (actual : evalHOLFinite current (h:=fun query => Classical.propDecidable (current.memaddrs query)) test = some (.val (.word observed)))
    (nonzero : observed ≠ 0#64) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState (decClockHOLFinite current) step = (result,target))
    (continuing : result = none ∨ result = some .continue) : ScanInvariant origin a b left right target := by
  obtain ⟨index,bounded,state⟩ := ready
  have active := scan_active state bounded observed actual nonzero
  have controls := (step_flow (ofString "key_len") (by decide) (by decide) (by decide)).summary (decClockHOLFinite current)
  have normalResult : result = none := by
    rcases continuing with fallthrough | continued
    · exact fallthrough
    · have impossible := controls.2.2
      rw [run] at impossible
      exact (impossible continued).elim
  have normal : evaluateHOLFiniteState (decClockHOLFinite current) step = (none,target) := by
    simpa only [normalResult] using run
  exact ⟨index+1,by omega,scan_step state.at_tick active aView bView normal⟩

/-- A full normal byte scan reached32 and all actual key bytes agreed. -/
theorem loop_none_equal (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (a b : BitVec 64) (left right : KeyBits.Key)
    (ready : ScanInvariant origin a b left right source)
    (aView : ByteView origin a left) (bView : ByteView origin b right)
    (normal : evaluateHOLFiniteState source loop = (none,post)) : Scan origin post a b left right 32 ∧ left = right := by
  rw [shapes.2.2.1] at normal
  apply loop_control_exit test step (ScanInvariant origin a b left right)
    (fun current => Scan origin current a b left right 32 ∧ left = right) _ _ _ source post ready normal
  · intro current valid stopped
    obtain ⟨index,bounded,state⟩ := valid
    have read := scan_test_read state bounded
    have full : index = 32 := by
      by_cases active : index < 32
      · rw [if_pos active] at read
        have impossible := stopped.symm.trans read
        cases impossible
      · omega
    subst index
    refine ⟨state,?_⟩
    funext prior
    exact state.earlier prior prior.isLt
  · intro current valid observed actual nonzero funded target result run continuing
    exact scan_progress valid aView bView observed actual nonzero result run continuing
  · intro current valid observed actual nonzero funded target run
    have controls := (step_flow (ofString "key_len") (by decide) (by decide) (by decide)).summary (decClockHOLFinite current)
    have impossible := controls.2.1
    rw [run] at impossible
    exact (impossible rfl).elim

/-- Actual loop returns establish the least difference without replacing
the source scan or supplying a hypothetical successful future iteration. -/
theorem loop_returned (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (a b : BitVec 64) (left right : KeyBits.Key)
    (ready : ScanInvariant origin a b left right source)
    (aView : ByteView origin a left) (bView : ByteView origin b right)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source loop = (some (.returned value),post)) : Answer left right value := by
  rw [shapes.2.2.1] at normal
  apply ReturnFacts.loop source.code test step (ScanInvariant origin a b left right) (Answer left right) _ _ source rfl ready post value normal
  · intro current installed valid observed actual nonzero funded target returned run
    obtain ⟨index,bounded,state⟩ := valid
    exact scan_step_returned state.at_tick (scan_active state bounded observed actual nonzero) aView bView returned run
  · intro current installed valid observed actual nonzero funded target result run continuing
    exact scan_progress valid aView bView observed actual nonzero result run continuing

end InitECandidate.Solver.Input.CurrentTable.FirstDiff

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.scan_step_returned
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.loop_none_equal
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.loop_returned
