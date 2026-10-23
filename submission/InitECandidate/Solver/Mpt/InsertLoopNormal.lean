import InitECandidate.Solver.Mpt.InsertIterationNormal

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every normal whole original insertion loop stops with its real
registered result, preserves every older graph member/tag and retains
its bounded actual heap and complete value/path model. -/
theorem loop_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (key length pointer size : BitVec 64) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (model : LoopModel source key length pointer size limit nodeLower pathLower property)
    (extra : property pointer size) (empty : property 0#64 0#64)
    (normal : evaluateHOLFiniteState source (.while test loopBody)=(none,target)) :
    ∃ next : LoopModel target key length pointer size limit nodeLower pathLower property,next.go=0#64 ∧
      model.heap.toNat≤next.heap.toNat ∧ (∀ node,model.graph.valid node → next.graph.valid node) ∧
      (∀ query : BitVec 64,query.toNat<nodeLower → target.memory query=source.memory query) ∧
      (∀ node,model.graph.valid node → node≠0#64 → wordAt target.memory node=wordAt source.memory node) := by
  have auxiliary : ∀ clock (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
      (model : LoopModel source key length pointer size limit nodeLower pathLower property),source.clock=clock →
      evaluateHOLFiniteState source (.while test loopBody)=(none,target) →
      ∃ next : LoopModel target key length pointer size limit nodeLower pathLower property,next.go=0#64 ∧
        model.heap.toNat≤next.heap.toNat ∧ (∀ node,model.graph.valid node → next.graph.valid node) ∧
        (∀ query : BitVec 64,query.toNat<nodeLower → target.memory query=source.memory query) ∧
        (∀ node,model.graph.valid node → node≠0#64 → wordAt target.memory node=wordAt source.memory node) := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih=>
      intro source target model clockEq normal
      rcases model.goTyped with stopped|going
      · have read : eval source test=some (.val (.word 0#64)):=by
          simp [eval,test,localVar,evalHOLExact,toExact,model.goCell,stopped,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        have skipped : evaluateHOLFiniteState source (.while test loopBody)=(none,source):=by
          rw [evaluateHOLFiniteState_while_total]
          simp only [eval,evalHOLFinite] at read ⊢
          rw [read]
          simp
        have targetEq : target=source:=congrArg Prod.snd (normal.symm.trans skipped)
        subst target
        exact ⟨model,stopped,Nat.le_refl _,(fun node live=>live),(by intro query before; rfl),(by intro node live active; rfl)⟩
      · have read : eval source test=some (.val (.word 1#64)):=by
          simp [eval,test,localVar,evalHOLExact,toExact,model.goCell,going,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        obtain ⟨funded,middle,bodyRun,tailRun,forward⟩:=Input.while_none_step source target (ofString "klen") test loopBody loop_body_safe read normal
        let entered : LoopModel (decClockHOLFinite source) key length pointer size limit nodeLower pathLower property:={model with}
        have active : entered.go≠0#64:=by change model.go≠0#64; rw [going]; decide
        obtain ⟨current,grows,members,memory,tags,progress⟩:=iteration_path_normal (decClockHOLFinite source) middle key length pointer size limit nodeLower pathLower property entered active extra empty bodyRun
        have smaller : middle.clock<clock:=by omega
        obtain ⟨next,stopped,finalGrows,finalMembers,finalMemory,finalTags⟩:=ih middle.clock smaller middle target current rfl tailRun
        exact ⟨next,stopped,grows.trans finalGrows,(fun node live=>finalMembers node (members node live)),
          (fun query before=>(finalMemory query before).trans (memory query before)),
          (fun node live active=>(finalTags node (members node live) active).trans (tags node live active))⟩
  exact auxiliary source.clock source target model rfl normal

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.loop_path_normal
