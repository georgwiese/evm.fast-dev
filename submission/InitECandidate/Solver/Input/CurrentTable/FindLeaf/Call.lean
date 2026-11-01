import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Context
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.ScopedCallClassified
import InitECandidate.Solver.Input.ClockCostTerminatingScoped

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

/-- Compose a range-bounded original lookup with its actual scoped
continuation. The same callee run supplies the returned in-range leaf and
full physical frame; no later successful lookup is assumed. -/
theorem RangeContext.scoped_price {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table base root width pointer : BitVec 64} {limit : Nat} {bits left right : BitVec 64 → BitVec 64}
    (ready : RangeContext source table base root width limit bits left right)
    (installed : OriginalCode.Installed source.code) (name : String)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some [.val (.word table), .val (.word pointer)])
    (tailCost : ∀ target leaf, leaf.toNat < limit → (leaf = 0#64 ∨ bits leaf = width * 8#64) →
      LocalEffects.erase target = LocalEffects.erase source → ∀ result final,
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word leaf))) continuation = (result, final) →
      result ≠ some .timeOut → target.clock - final.clock ≤ tailPrice)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_find_leaf") arguments continuation) = (result, post))
    (notTimeout : result ≠ some .timeOut) : source.clock - post.clock ≤ limit + tailPrice + 1 := by
  obtain ⟨callee, called, tableCell, pointerCell⟩ := word_pair_environment source.code.lookup
    (ofString "htab_find_leaf") (ofString "t") (ofString "key") body .one table pointer (by decide)
    (original_code source.code installed)
  have current : RangeContext (callEntryStateHOLFinite source callee) table base root width limit bits left right := ready.of_frame rfl
  exact ClockCost.scoped_reached_terminating source post name .one (ofString "htab_find_leaf") arguments _ body continuation callee .one
    limit tailPrice args called
    (by intro observed target evaluated noTimeout
        have observedNotTimeout : (evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).1 ≠ some .timeOut := by
          rw [evaluated]
          exact noTimeout
        have price := current.price tableCell pointerCell observedNotTimeout
        rw [evaluated] at price
        exact price)
    (by intro target value normal checked outcome final continued noTimeout
        obtain ⟨leaf, answer, inside, finished, frame⟩ := current.returned tableCell pointerCell value normal
        rw [answer] at continued
        exact tailCost target leaf inside finished frame outcome final continued noTimeout)
    result run notTimeout

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.scoped_trace
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.scoped_returned
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.RangeContext.scoped_price
