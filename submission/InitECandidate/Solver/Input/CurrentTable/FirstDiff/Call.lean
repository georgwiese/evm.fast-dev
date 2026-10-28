import InitECandidate.Solver.Input.CurrentTable.FirstDiff.Entry
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.ScopedCallClassified

namespace InitECandidate.Solver.Input.CurrentTable.FirstDiff
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every actual current32-byte scoped outcome stops within289source
clocks or reaches its original continuation with the real least difference,
full physical frame and actual caller/clock restoration. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (a b : BitVec 64) (left right : KeyBits.Key)
    (aView : ByteView source a left) (bView : ByteView source b right)
    (installed : OriginalCode.Installed source.code)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query => Classical.propDecidable (source.memaddrs query)) expressions =
      some [.val (.word a),.val (.word b),.val (.word 32#64)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_first_diff") expressions continuation) = (outcome,post)) :
    (source.clock-post.clock ≤ 289 ∧ ∀ value,outcome ≠ some (.returned value)) ∨
      ∃ target inner,LocalEffects.erase target = LocalEffects.erase source ∧
        target.clock ≤ source.clock ∧ source.clock-target.clock ≤ 289 ∧
        evaluateHOLFiniteState (CallNormal.continuationEntry source target name
          (.val (.word (BitVec.ofNat 64 (KeyBits.first left right))))) continuation = (outcome,inner) ∧ post = restore source name inner := by
  obtain ⟨callee,called,aCell,bCell,lengthCell⟩ := word_triple_environment source.code.lookup
    (ofString "htab_first_diff") (ofString "a") (ofString "b") (ofString "key_len") body .one
    a b 32#64 (by decide) (by decide) (by decide) (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have price : entry.clock-(evaluateHOLFiniteState entry body).2.clock ≤ 288 := by
    simpa using body_cost entry 32 (by decide) lengthCell
  rcases CallNormal.scoped_classified source post name .one (ofString "htab_first_diff") expressions _ body continuation callee .one 288
    args called price outcome run with stopped | reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩ := reached
    obtain ⟨answer,frame⟩ := body_first entry target a b left right aCell bCell lengthCell
      (aView.of_frame rfl) (bView.of_frame rfl) value bodyRun
    rw [answer] at continued
    exact Or.inr ⟨target,inner,frame,forward,cost,continued,endpoint⟩

theorem scoped_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (a b : BitVec 64) (left right : KeyBits.Key)
    (aView : ByteView source a left) (bView : ByteView source b right)
    (installed : OriginalCode.Installed source.code)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query => Classical.propDecidable (source.memaddrs query)) expressions =
      some [.val (.word a),.val (.word b),.val (.word 32#64)])
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_first_diff") expressions continuation) = (some (.returned value),post)) :
    ∃ target inner,LocalEffects.erase target = LocalEffects.erase source ∧
      target.clock ≤ source.clock ∧ source.clock-target.clock ≤ 289 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name
        (.val (.word (BitVec.ofNat 64 (KeyBits.first left right))))) continuation = (some (.returned value),inner) ∧ post = restore source name inner := by
  rcases scoped_trace source post a b left right aView bView installed name expressions continuation args (some (.returned value)) run with stopped | reached
  · exact (stopped.2 value rfl).elim
  · exact reached

end InitECandidate.Solver.Input.CurrentTable.FirstDiff

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.scoped_trace
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.scoped_returned
