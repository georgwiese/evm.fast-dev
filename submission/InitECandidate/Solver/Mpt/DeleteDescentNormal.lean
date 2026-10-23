import InitECandidate.Solver.Mpt.DeleteDescentIteration
import InitECandidate.Solver.Mpt.DeleteDescentSafety
import InitECandidate.Solver.Mpt.DeleteDescentOutputCompose

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole original descent loop, by actual remaining-query progress.
Every genuine normal return has stopped go and retains the complete
physical trie/query/pending-stack invariant. Shared or cyclic children
need no pointer order: each nonterminal step consumes key nibbles. -/
theorem descent_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (empty : property 0#64 0#64)
    (normal : evaluateHOLFiniteState source descent=(none,target)) :
    Nonempty {output : DescentOutput source target key length limit nodeLower pathLower property model // output.next.go=0#64} := by
  have auxiliary : ∀ budget (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
      (model : DescentModel source key length limit nodeLower pathLower property),
      (if model.go=0#64 then 0 else length.toNat-model.level.toNat+1)=budget→
      evaluateHOLFiniteState source (.while descentTest descentBody)=(none,target)→
      Nonempty {output : DescentOutput source target key length limit nodeLower pathLower property model // output.next.go=0#64} := by
    intro budget
    induction budget using Nat.strong_induction_on with
    | h budget ih=>
      intro source target model budgetEq normal
      by_cases stopped : model.go=0#64
      · have read : eval source descentTest=some (.val (.word 0#64)):=by
          simp [eval,descentTest,localVar,evalHOLExact,toExact,model.goCell,stopped,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        have skipped : evaluateHOLFiniteState source (.while descentTest descentBody)=(none,source):=by
          rw [evaluateHOLFiniteState_while_total]
          simp only [eval,evalHOLFinite] at read ⊢
          rw [read]
          simp
        have targetEq : target=source:=congrArg Prod.snd (normal.symm.trans skipped)
        subst target
        exact ⟨⟨{
          next:=model
          grows:=Nat.le_refl _
          scratchDecreases:=Nat.le_refl _
          frameEq:=rfl
          members:=fun _ member=>member
          freshMembers:=fun _ member=>Or.inl member
          fields:=TrieWalk.Graph.PathFields.of_agreement model.pending.graph source.memory (fun _ _=>rfl)
          memoryLow:=fun _ _=>rfl
          memoryBand:=fun _ _ _=>rfl
          protectedWords:=by intro address safe _above _before; exact ⟨rfl,safe⟩
          globals:=fun _ _ _=>rfl
          progress:=Or.inl stopped },stopped⟩⟩
      · have read : eval source descentTest=some (.val (.word 1#64)):=by
          simp [eval,descentTest,localVar,evalHOLExact,toExact,model.goCell,stopped,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        obtain ⟨_funded,middle,bodyRun,tailRun,_forward⟩:=Input.while_none_step source target (ofString "key") descentTest descentBody descent_body_safe read normal
        let entered:=model.with_clock source key length limit nodeLower pathLower property (source.clock-1)
        obtain ⟨front⟩:=descent_iteration_normal (decClockHOLFinite source) middle key length limit nodeLower pathLower property entered empty bodyRun
        let nextBudget:=if front.next.go=0#64 then 0 else length.toNat-front.next.level.toNat+1
        have smaller : nextBudget<budget:=by
          rw [if_neg stopped] at budgetEq
          by_cases done : front.next.go=0#64
          · simp only [nextBudget,if_pos done]
            omega
          · have progress : model.level.toNat<front.next.level.toNat:=by
              rcases front.progress with terminal|increases
              · exact (done terminal).elim
              · exact increases
            have before:=front.next.levelBound
            simp only [nextBudget,if_neg done]
            omega
        obtain ⟨⟨back,done⟩⟩:=ih nextBudget smaller middle target front.next rfl tailRun
        let initial : DescentOutput source middle key length limit nodeLower pathLower property model:={front with next:=front.next}
        exact DescentOutput.then_stopped source middle target key length limit nodeLower pathLower property model initial back done
  rw [descent_shapes.1] at normal
  exact auxiliary (if model.go=0#64 then 0 else length.toNat-model.level.toNat+1) source target model rfl normal

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_path_normal
