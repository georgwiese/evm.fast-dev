import InitECandidate.Solver.Mpt.CommonPrefixCost
import InitECandidate.Solver.Input.LoopReturnedProperty
import InitECandidate.Solver.Input.ReturnGuardNormal
import InitECandidate.Solver.Input.ContinuingDeclarationEntry

namespace InitECandidate.Solver.Mpt.CommonPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem loop_body_return (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (index : BitVec 64)
    (iCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source loopBody=(some (.returned value),target)) :
    value=.val (.word index) := by
  obtain early|impossible:=Input.return_guard_normal source target mismatch (localVar "i") advance value normal
  · have actual : eval source (localVar "i")=some (.val (.word index)):=by simp [eval,localVar,evalHOLExact,toExact,iCell]
    exact Option.some.inj (early.1.symm.trans actual)
  · have safe : Input.LocalPrefix (ofString "n") advance:=.assign _ _ (by decide)
    exact ((safe.summary_full source).2.1 value (congrArg Prod.fst impossible)).elim

theorem loop_return_bound (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length≤64) (valid : Input.GuardedCounterLoop.Invariant length source)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (.while test loopBody)=(some (.returned value),target)) :
    ∃ word : BitVec 64,value=.val (.word word) ∧ word.toNat≤length := by
  apply Input.loop_returned_property source.code test loopBody guarded.no_control (Input.GuardedCounterLoop.Invariant length)
    (fun value _=>∃ word : BitVec 64,value=.val (.word word) ∧ word.toNat≤length) _ _ source target value rfl valid normal
  · intro current codeEq ready observed read nonzero funded post bodyRun
    have next:=(Input.GuardedCounterLoop.transition test loopBody 1 length (by decide) small guarded (test_reads length small)
      current ready observed read nonzero).2 funded
    rw [bodyRun] at next
    exact (next (Or.inl rfl)).1
  · intro current codeEq ready observed read nonzero funded post returned bodyRun
    obtain ⟨index,iCell,nCell,bound⟩:=ready
    exact ⟨index,loop_body_return (decClockHOLFinite current) post index iCell returned bodyRun,bound⟩

theorem loop_and_after_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length≤64) (valid : Input.GuardedCounterLoop.Invariant length source)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source loopAndAfter=(some (.returned value),target)) :
    ∃ word : BitVec 64,value=.val (.word word) ∧ word.toNat≤length := by
  rw [loopAndAfter,evaluateHOLFiniteState_seq_line780] at normal
  generalize computed : evaluateHOLFiniteState source (.while test loopBody)=output at normal
  obtain ⟨result,middle⟩:=output
  cases result with
  | none=>
    have next:=Input.GuardedCounterLoop.normal test loopBody 1 length (by decide) small guarded (test_reads length small) source middle valid computed
    obtain ⟨index,iCell,nCell,bound⟩:=next
    obtain ⟨read,endpoint⟩:=Input.return_normal middle target (localVar "n") value normal
    have actual : eval middle (localVar "n")=some (.val (.word (BitVec.ofNat 64 length))):=by simp [eval,localVar,evalHOLExact,toExact,nCell]
    refine ⟨BitVec.ofNat 64 length,Option.some.inj (read.symm.trans actual),?_⟩
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  | some result=>
    have resultEq : result=.returned value:=Option.some.inj (congrArg Prod.fst normal)
    subst result
    exact loop_return_bound source middle length small valid value computed

end InitECandidate.Solver.Mpt.CommonPrefix

#print axioms InitECandidate.Solver.Mpt.CommonPrefix.loop_body_return
#print axioms InitECandidate.Solver.Mpt.CommonPrefix.loop_return_bound
#print axioms InitECandidate.Solver.Mpt.CommonPrefix.loop_and_after_normal
