import InitECandidate.Solver.Mpt.DeleteUnwindIteration
import InitECandidate.Solver.Mpt.DeleteUnwindSafety

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole original return-unwind loop, with induction on the actual
physical frame count. Every normal result has popped the complete stack,
retaining the current registered result and all old parent/path facts. -/
theorem unwind_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : UnwindModel source limit nodeLower pathLower property)
    (normal : evaluateHOLFiniteState source unwind=(none,target)) :
    ∃ next : UnwindModel target limit nodeLower pathLower property,next.top=0#64 ∧ next.frames=[] ∧
      model.heap.toNat≤next.heap.toNat ∧ (∀ node,model.graph.valid node→next.graph.valid node) ∧
      model.graph.PathFields target.memory ∧
      (∀ query : BitVec 64,query.toNat<nodeLower→target.memory query=source.memory query) ∧
      (∀ key,key≠ofString "heap_ptr"→target.globals.lookup key=source.globals.lookup key) := by
  have auxiliary : ∀ depth (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
      (model : UnwindModel source limit nodeLower pathLower property),model.frames.length=depth→
      evaluateHOLFiniteState source (.while unwindTest unwindBody)=(none,target)→
      ∃ next : UnwindModel target limit nodeLower pathLower property,next.top=0#64 ∧ next.frames=[] ∧
        model.heap.toNat≤next.heap.toNat ∧ (∀ node,model.graph.valid node→next.graph.valid node) ∧
        model.graph.PathFields target.memory ∧
        (∀ query : BitVec 64,query.toNat<nodeLower→target.memory query=source.memory query) ∧
        (∀ key,key≠ofString "heap_ptr"→target.globals.lookup key=source.globals.lookup key) := by
    intro depth
    induction depth using Nat.strong_induction_on with
    | h depth ih=>
      intro source target model depthEq normal
      by_cases stopped : model.top=0#64
      · have read : eval source unwindTest=some (.val (.word 0#64)):=by
          simp [eval,unwindTest,localVar,evalHOLExact,toExact,model.topCell,stopped,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        have skipped : evaluateHOLFiniteState source (.while unwindTest unwindBody)=(none,source):=by
          rw [evaluateHOLFiniteState_while_total]
          simp only [eval,evalHOLFinite] at read ⊢
          rw [read]
          simp
        have targetEq : target=source:=congrArg Prod.snd (normal.symm.trans skipped)
        subst target
        exact ⟨model,stopped,(model.empty_iff source limit nodeLower pathLower property).2 stopped,Nat.le_refl _,(fun _ live=>live),
          TrieWalk.Graph.PathFields.of_agreement model.graph source.memory (fun _ _=>rfl),(fun _ _=>rfl),(fun _ _=>rfl)⟩
      · have read : eval source unwindTest=some (.val (.word 1#64)):=by
          simp [eval,unwindTest,localVar,evalHOLExact,toExact,model.topCell,stopped,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        obtain ⟨_funded,middle,bodyRun,tailRun,_forward⟩:=Input.while_none_step source target (ofString "key") unwindTest unwindBody unwind_body_safe read normal
        let entered:=model.with_clock source limit nodeLower pathLower property (source.clock-1)
        obtain ⟨current,decreases,grows,members,fields,memory,globals⟩:=unwind_iteration_normal (decClockHOLFinite source) middle limit nodeLower pathLower property entered stopped bodyRun
        have smaller : current.frames.length<depth:=by change current.frames.length+1=model.frames.length at decreases; omega
        obtain ⟨next,topZero,empty,finalGrows,finalMembers,finalFields,finalMemory,finalGlobals⟩:=ih current.frames.length smaller middle target current rfl tailRun
        have composedFields : model.graph.PathFields target.memory:=fields.trans model.graph current.graph finalFields members
        exact ⟨next,topZero,empty,grows.trans finalGrows,(fun node live=>finalMembers node (members node live)),composedFields,
          (fun query before=>(finalMemory query before).trans (memory query before)),
          (fun key other=>(finalGlobals key other).trans (globals key other))⟩
  rw [unwind_shapes.1] at normal
  exact auxiliary model.frames.length source target model rfl normal

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.unwind_path_normal
