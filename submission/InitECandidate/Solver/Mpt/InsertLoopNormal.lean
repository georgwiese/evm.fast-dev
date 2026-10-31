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
      (∀ node,model.graph.valid node → node≠0#64 → wordAt target.memory node=wordAt source.memory node) ∧
      model.graph.PathFields target.memory ∧
      (∀ address : BitVec 64,(model.go≠0#64 → model.graph.ProtectedWord address) → address.toNat<model.heap.toNat → target.memory address=source.memory address) ∧
      (∀ node,next.graph.valid node → model.graph.valid node ∨ model.heap.toNat≤node.toNat) ∧
      (∀ address : BitVec 64,model.graph.ProtectedWord address → address.toNat<model.heap.toNat →
        TrieWalk.PathWordAway key length.toNat address → next.graph.ProtectedWord address) ∧
      ((model.result≠0#64 ∨ (model.go≠0#64 ∧ model.slot=0#64)) → next.result≠0#64) ∧
      (((model.result≠0#64 → wordAt source.memory model.result≠0#64) ∨ (model.go≠0#64 ∧ model.slot=0#64)) →
        next.result≠0#64 → wordAt target.memory next.result≠0#64) := by
  have auxiliary : ∀ clock (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
      (model : LoopModel source key length pointer size limit nodeLower pathLower property),source.clock=clock →
      evaluateHOLFiniteState source (.while test loopBody)=(none,target) →
      ∃ next : LoopModel target key length pointer size limit nodeLower pathLower property,next.go=0#64 ∧
        model.heap.toNat≤next.heap.toNat ∧ (∀ node,model.graph.valid node → next.graph.valid node) ∧
        (∀ query : BitVec 64,query.toNat<nodeLower → target.memory query=source.memory query) ∧
        (∀ node,model.graph.valid node → node≠0#64 → wordAt target.memory node=wordAt source.memory node) ∧
      model.graph.PathFields target.memory ∧
      (∀ address : BitVec 64,(model.go≠0#64 → model.graph.ProtectedWord address) → address.toNat<model.heap.toNat → target.memory address=source.memory address) ∧
      (∀ node,next.graph.valid node → model.graph.valid node ∨ model.heap.toNat≤node.toNat) ∧
      (∀ address : BitVec 64,model.graph.ProtectedWord address → address.toNat<model.heap.toNat →
        TrieWalk.PathWordAway key length.toNat address → next.graph.ProtectedWord address) ∧
      ((model.result≠0#64 ∨ (model.go≠0#64 ∧ model.slot=0#64)) → next.result≠0#64) ∧
      (((model.result≠0#64 → wordAt source.memory model.result≠0#64) ∨ (model.go≠0#64 ∧ model.slot=0#64)) →
        next.result≠0#64 → wordAt target.memory next.result≠0#64) := by
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
        exact ⟨model,stopped,Nat.le_refl _,(fun node live=>live),(by intro query before; rfl),(by intro node live active; rfl),
          ⟨by intro node live active; rfl,by intro node live active tag; exact ⟨rfl,rfl⟩⟩,
          (by intro address _safe _before; rfl),
          (by intro node live; exact Or.inl live),(by intro address safe _before _away; exact safe),
          (by intro incoming; exact incoming.elim id (fun live=>(live.1 stopped).elim)),
          (by intro incoming live; exact incoming.elim (fun kind=>kind live) (fun running=>(running.1 stopped).elim))⟩
      · have read : eval source test=some (.val (.word 1#64)):=by
          simp [eval,test,localVar,evalHOLExact,toExact,model.goCell,going,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        obtain ⟨funded,middle,bodyRun,tailRun,forward⟩:=Input.while_none_step source target (ofString "klen") test loopBody loop_body_safe read normal
        let entered : LoopModel (decClockHOLFinite source) key length pointer size limit nodeLower pathLower property:={model with}
        have active : entered.go≠0#64:=by change model.go≠0#64; rw [going]; decide
        obtain ⟨current,grows,members,memory,tags,progress,fields,protectedWords,registry,provenance,protection,positive,kind⟩:=iteration_path_normal (decClockHOLFinite source) middle key length pointer size limit nodeLower pathLower property entered active extra empty bodyRun
        have smaller : middle.clock<clock:=by omega
        obtain ⟨next,stopped,finalGrows,finalMembers,finalMemory,finalTags,finalFields,finalWords,finalFresh,finalProtection,finalPositive,finalKind⟩:=ih middle.clock smaller middle target current rfl tailRun
        exact ⟨next,stopped,grows.trans finalGrows,(fun node live=>finalMembers node (members node live)),
          (fun query before=>(finalMemory query before).trans (memory query before)),
          (fun node live active=>(finalTags node (members node live) active).trans (tags node live active)),
          fields.trans model.graph current.graph finalFields members,
          (by
            intro address safe before
            have oldSafe : model.graph.ProtectedWord address:=safe (by rw [going]; decide)
            have currentSafe : current.go≠0#64 → current.graph.ProtectedWord address:=by
              intro running
              exact oldSafe.of_fields model.graph current.graph address (registry running) fields
            exact (finalWords address currentSafe (before.trans_le grows)).trans (protectedWords address oldSafe before)),
          (by
            intro node live
            rcases finalFresh node live with old|fresh
            · exact provenance node old
            · exact Or.inr (grows.trans fresh)),
          (by
            intro address safe before away
            exact finalProtection address (protection address safe before away) (before.trans_le grows) away),
          (by
            intro incoming
            have currentPositive : current.result≠0#64:=positive (incoming.elim Or.inr (fun live=>Or.inl live.2))
            exact finalPositive (Or.inl currentPositive)),
          (by
            intro incoming live
            have currentKind : current.result≠0#64 → wordAt middle.memory current.result≠0#64 :=
              kind (incoming.elim Or.inr (fun running=>Or.inl running.2))
            exact finalKind (Or.inl currentKind) live)⟩
  exact auxiliary source.clock source target model rfl normal

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.loop_path_normal
