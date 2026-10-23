import InitECandidate.Solver.Mpt.IndexedLoopCost
import InitECandidate.Solver.Input.LoopNormal

namespace InitECandidate.Solver.Mpt.Indexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A normal whole update loop reaches the real input count and retains
its complete live map/trie, original rows and every older persistent word
outside the fixed startup scratch buffers. -/
theorem loop_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (m array : BitVec 64)
    (count cutoff limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop)
    (model : LoopModel source m array count cutoff limit slices property)
    (normal : evaluateHOLFiniteState source (.while test loopBody)=(none,target)) :
    ∃ next : LoopModel target m array count cutoff limit slices property,next.index.toNat=count ∧ model.heap.toNat≤next.heap.toNat ∧
      (∀ query : BitVec 64,2713731432≤query.toNat→query.toNat<cutoff→target.memory query=source.memory query) := by
  have auxiliary : ∀ clock (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
      (model : LoopModel source m array count cutoff limit slices property),source.clock=clock→
      evaluateHOLFiniteState source (.while test loopBody)=(none,target)→
      ∃ next : LoopModel target m array count cutoff limit slices property,next.index.toNat=count ∧ model.heap.toNat≤next.heap.toNat ∧
        (∀ query : BitVec 64,2713731432≤query.toNat→query.toNat<cutoff→target.memory query=source.memory query):=by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih=>
      intro source target model clockEq normal
      by_cases active : model.index.toNat<count
      · have read : eval source test=some (.val (.word 1#64)):=by
          have actual:=test_read source model.index count model.countBound model.indexCell model.countCell
          rwa [if_pos active] at actual
        obtain ⟨_funded,middle,bodyRun,tailRun,forward⟩:=Input.while_none_step source target (ofString "n") test loopBody loop_body_limit read normal
        obtain ⟨entered,indexEq,heapEq⟩:=model.dec_clock source m array count cutoff limit slices property
        obtain ⟨current,_advance,grows,memory⟩:=iteration_normal (decClockHOLFinite source) middle m array count cutoff limit slices property entered (by rw [indexEq]; exact active) bodyRun
        obtain ⟨next,finished,finalGrows,finalMemory⟩:=ih middle.clock (by omega) middle target current rfl tailRun
        exact ⟨next,finished,(by rw [←heapEq]; exact grows.trans finalGrows),by
          intro query above before
          exact (finalMemory query above before).trans (memory query above before)⟩
      · have read : eval source test=some (.val (.word 0#64)):=by
          have actual:=test_read source model.index count model.countBound model.indexCell model.countCell
          rwa [if_neg active] at actual
        have skipped : evaluateHOLFiniteState source (.while test loopBody)=(none,source):=by
          rw [evaluateHOLFiniteState_while_total]
          simp only [eval,evalHOLFinite] at read ⊢
          rw [read]
          simp
        have same : target=source:=congrArg Prod.snd (normal.symm.trans skipped)
        subst target
        exact ⟨model,by have bound:=model.bounded; omega,Nat.le_refl _,by intros; rfl⟩
  exact auxiliary source.clock source target model rfl normal

end InitECandidate.Solver.Mpt.Indexed

#print axioms InitECandidate.Solver.Mpt.Indexed.loop_normal
