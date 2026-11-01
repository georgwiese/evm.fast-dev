import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Loop
import InitECandidate.Solver.Input.LoopControlExit
import InitECandidate.Solver.Input.NoReturnDecision
import InitECandidate.Solver.Input.ReturnFactsLoop

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The original step contains no caller return, even on arbitrary inputs. -/
theorem step_never : NoReturn.Never step := by
  rw [shapes.2.1,shapes.2.2.1]
  apply NoReturn.declared
  apply NoReturn.sequence
  · exact NoReturn.conditional _ _ _ NoReturn.breaks NoReturn.skip
  · intro F source value
    exact (branch_safe.summary_full source).2.1 value

/-- The actual body can break only at the leaf marker, retaining the same
node and physical state while restoring its temporary b binding. -/
theorem step_break {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64} {marker : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : Nodes origin base valid bits left right marker.toNat) (ready : State origin source base node marker) (member : valid node)
    (run : evaluateHOLFiniteState source step=(some .break,post)) : bits node=marker.toNat ∧ post=source := by
  let entered:=bind source "b" (BitVec.ofNat 64 (bits node))
  have current:=ready.with_bit (BitVec.ofNat 64 (bits node))
  have bitCell : entered.locals.lookup (ofString "b")=some (.val (.word (BitVec.ofNat 64 (bits node)))) := bind_lookup_same _ _ _
  have afterRun:=after_bit_execute_marker marker entered (bits node) (image.bitBound node member) bitCell current.bitsCell
  by_cases leaf : bits node=marker.toNat
  · rw [if_pos leaf] at afterRun
    have actual:=ScalarScope.declare_execute source entered "b" (.load .one (address 24)) (BitVec.ofNat 64 (bits node)) afterBit (some .break) (bit_read image ready member) afterRun
    rw [shapes.2.1,actual] at run
    have endpoint:=congrArg Prod.snd run
    dsimp only at endpoint
    exact ⟨leaf,by rw [←endpoint,restore_bound]⟩
  · rw [if_neg leaf] at afterRun
    let output:=evaluateHOLFiniteState entered branch
    have actual:=ScalarScope.declare_execute source output.2 "b" (.load .one (address 24)) (BitVec.ofNat 64 (bits node)) afterBit output.1 (bit_read image ready member) afterRun
    rw [shapes.2.1,actual] at run
    have equal:=congrArg Prod.fst run
    dsimp only at equal
    exact ((branch_safe.summary_full entered).2.2.1 equal).elim

def Finished (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (marker : BitVec 64:=256#64) : Prop :=
  ∃ node,State origin source base node marker ∧ (node=0#64 ∨ valid node ∧ bits node=marker.toNat)

theorem active_node (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node observed : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "n")=some (.val (.word node)))
    (read : evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=some (.val (.word observed)))
    (nonzero : observed≠0#64) : node≠0#64 := by
  intro zero
  have expected:=test_read source node nodeCell
  rw [if_pos zero] at expected
  have equal : observed=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero equal

/-- A genuinely normal loop exit has either zero or an actual leaf node.
A body break is handled through its real marker rather than excluded. -/
theorem loop_finished {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {marker : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : Nodes origin base valid bits left right marker.toNat) (ready : Invariant origin base valid source marker)
    (normal : evaluateHOLFiniteState source loop=(none,post)) : Finished origin post base valid bits marker := by
  rw [shapes.1] at normal
  apply loop_control_exit test step (fun current=>Invariant origin base valid current marker) (fun current=>Finished origin current base valid bits marker) _ _ _ source post ready normal
  · intro current state read
    obtain ⟨node,live,present⟩:=state
    have expected:=test_read current node live.nodeCell
    have equal : (if node=0#64 then 0#64 else 1#64)=(0#64 : BitVec 64) := by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using expected.symm.trans read
    have zero : node=0#64 := by
      by_cases zero : node=0#64
      · exact zero
      · rw [if_neg zero] at equal
        exact ((by decide : (1#64 : BitVec 64)≠0#64) equal).elim
    exact ⟨node,live,Or.inl zero⟩
  · intro current state observed read nonzero funded target result run continuing
    have info:=(transition image current state observed read nonzero).2 funded
    rw [run] at info
    exact (info continuing).1
  · intro current state observed read nonzero funded target run
    obtain ⟨node,live,present⟩:=state
    have member:=present.resolve_left (active_node current node observed live.nodeCell read nonzero)
    obtain ⟨leaf,endpoint⟩:=step_break image live.at_tick member run
    rw [endpoint]
    exact ⟨node,live.at_tick,Or.inr ⟨member,leaf⟩⟩

/-- The loop body has no return on any input. No table image is needed. -/
theorem loop_never_any (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    ∀ value, (evaluateHOLFiniteState source loop).1 ≠ some (.returned value) := by
  have returns := ReturnFacts.loop source.code test step (fun _ => True) (fun _ => False)
    (by intro current codeEq state observed read nonzero funded target value run
        exact step_never _ value (congrArg Prod.fst run))
    (by intro current codeEq state observed read nonzero funded target result run continuing
        trivial) source rfl True.intro
  intro value observed
  rw [shapes.1] at observed
  exact returns _ value (Prod.ext observed rfl)

/-- Legacy ordered-image interface to the unconditional no-return fact. -/
theorem loop_never {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {marker : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : Nodes origin base valid bits left right marker.toNat) (ready : Invariant origin base valid source marker) :
    ∀ value,(evaluateHOLFiniteState source loop).1≠some (.returned value) := loop_never_any source

/-- Normal exits retain a real in-range node and stop only at zero or at
the actual leaf marker, without an increasing-bit assumption. -/
theorem range_loop_finished {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base key marker : BitVec 64} {limit : Nat} {bits left right : BitVec 64 → BitVec 64}
    (image : RangeNodes origin base marker limit bits left right)
    (ready : RangeInvariant origin base key marker limit source)
    (normal : evaluateHOLFiniteState source loop = (none, post)) :
    ∃ node, State origin post base node marker ∧
      post.locals.lookup (ofString "key") = some (.val (.word key)) ∧ node.toNat < limit ∧
      (node = 0#64 ∨ bits node = marker) := by
  rw [shapes.1] at normal
  apply loop_control_exit test step (RangeInvariant origin base key marker limit)
    (fun current => ∃ node, State origin current base node marker ∧
      current.locals.lookup (ofString "key") = some (.val (.word key)) ∧ node.toNat < limit ∧
      (node = 0#64 ∨ bits node = marker)) _ _ _ source post ready normal
  · intro current state read
    obtain ⟨node, state, keyCell, inside⟩ := state
    have expected := test_read current node state.nodeCell
    have zero : node = 0#64 := by
      by_contra nonzero
      rw [if_neg nonzero] at expected
      have impossible : (1#64 : BitVec 64) = 0#64 := by
        simpa only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using expected.symm.trans read
      exact (by decide : (1#64 : BitVec 64) ≠ 0#64) impossible
    exact ⟨node, state, keyCell, inside, Or.inl zero⟩
  · intro current state observed read nonzero funded target result run continuing
    obtain ⟨node, state, keyCell, inside⟩ := state
    have model := range_step_model (by omega : 0 < limit) image state.at_tick keyCell (state.active read nonzero) inside
    rw [run] at model
    exact (model.1 continuing).1
  · intro current state observed read nonzero funded target run
    obtain ⟨node, state, keyCell, inside⟩ := state
    rw [range_step_execute image state.at_tick keyCell (state.active read nonzero) inside] at run
    by_cases leaf : bits node = marker
    · rw [if_pos leaf] at run
      have endpoint := congrArg Prod.snd run
      change decClockHOLFinite current = target at endpoint
      rw [← endpoint]
      exact ⟨node, state.at_tick, keyCell, inside, Or.inr leaf⟩
    · rw [if_neg leaf] at run
      generalize observed : keyProbe origin key (bits node) = value at run
      cases value with
      | none => cases run
      | some value =>
        cases value with
        | rStruct fields => cases run
        | nStruct name fields => cases run
        | val payload => cases payload; cases run

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.step_never
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.step_break
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.loop_finished
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.loop_never
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.loop_never_any
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.range_loop_finished
