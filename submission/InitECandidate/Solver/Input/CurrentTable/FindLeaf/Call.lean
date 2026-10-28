import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Context
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.ScopedCallClassified

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Every actual scoped outcome either stops within its allowance or
supplies zero/an actual leaf and the genuine original continuation. The
same full nonlocal frame protects the caller's table and input. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (table key base root : BitVec 64)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (context : Context source table base root valid bits left right) (installed : OriginalCode.Installed source.code)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some [.val (.word table),.val (.word key)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_find_leaf") expressions continuation)=(outcome,post)) :
    (source.clock-post.clock≤258 ∧ ∀ value,outcome≠some (.returned value)) ∨ ∃ target leaf inner,
      (leaf=0#64 ∨ valid leaf ∧ bits leaf=256) ∧ LocalEffects.erase target=LocalEffects.erase source ∧
      target.clock≤source.clock ∧ source.clock-target.clock≤258 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word leaf))) continuation=(outcome,inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,tableCell,keyCell⟩:=word_pair_environment source.code.lookup (ofString "htab_find_leaf") (ofString "t") (ofString "key") body .one table key (by decide) (original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have ready : Context entry table base root valid bits left right := context.of_frame rfl
  have price:=ready.price tableCell
  rcases CallNormal.scoped_classified source post name .one (ofString "htab_find_leaf") expressions _ body continuation callee .one 257 args called price outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩:=reached
    obtain ⟨leaf,answer,finished,frame⟩:=ready.returned tableCell value bodyRun
    rw [answer] at continued
    exact Or.inr ⟨target,leaf,inner,finished,frame,forward,cost,continued,endpoint⟩

theorem scoped_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (table key base root : BitVec 64)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (context : Context source table base root valid bits left right) (installed : OriginalCode.Installed source.code)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some [.val (.word table),.val (.word key)])
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_find_leaf") expressions continuation)=(some (.returned value),post)) :
    ∃ target leaf inner,(leaf=0#64 ∨ valid leaf ∧ bits leaf=256) ∧ LocalEffects.erase target=LocalEffects.erase source ∧
      target.clock≤source.clock ∧ source.clock-target.clock≤258 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word leaf))) continuation=(some (.returned value),inner) ∧ post=restore source name inner := by
  rcases scoped_trace source post table key base root valid bits left right context installed name expressions continuation args (some (.returned value)) run with stopped|reached
  · exact (stopped.2 value rfl).elim
  · exact reached

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.scoped_trace
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.scoped_returned
