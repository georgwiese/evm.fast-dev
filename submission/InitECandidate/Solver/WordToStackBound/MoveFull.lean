import InitECandidate.Solver.WordToStackBound.Common
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.MoveFull

namespace InitECandidate.Solver.WordToStackBound.MoveFull
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.MoveFull

theorem compCorrectMove {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (priority : Nat) (moves : List (Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Simulation ac limit (.move priority moves) source := by
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  obtain ⟨values,distinct,reads,rfl,rfl⟩ :=
    Move.sourceSuccess priority moves source sourcePost result execution notError
  have evens : (∀ n ∈ moves.map Prod.fst, n % 2=0) ∧
      (∀ n ∈ moves.map Prod.snd, n % 2=0) := by
    have raw : (∀ a b, (a,b) ∈ moves → a % 2=0) ∧
        (∀ a b, (a,b) ∈ moves → b % 2=0) := by
      simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
        callArgConventionHOL,isPhyVar,List.all_eq_true] using conventions
    constructor
    · intro n member
      obtain ⟨⟨a,b⟩,input,rfl⟩ := List.mem_map.mp member
      exact raw.1 a b input
    · intro n member
      obtain ⟨⟨a,b⟩,input,rfl⟩ := List.mem_map.mp member
      exact raw.2 a b input
  have wf : sptWf source.locals=true := by
    unfold stateRel at related
    tauto
  obtain ⟨post,run,relation,_,_⟩ := Move.actualScheduledRun ac k f frame lens moves source target
    related distinct evens.1 evens.2 (by simp [reads]) (by simpa [maxVarHOL] using maxBound)
  rw [Move.scheduledSourceStateReconstruction moves source target k values distinct
    evens.1 evens.2 reads wf] at relation
  have program := congrArg Prod.fst compilation
  simp only [compNative] at program
  subst compiled
  refine ⟨0,post,none,Nat.zero_le _,?_,?_⟩
  · simpa only [Nat.add_zero] using run
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,↓reduceIte] using relation
end InitECandidate.Solver.WordToStackBound.MoveFull
#print axioms InitECandidate.Solver.WordToStackBound.MoveFull.compCorrectMove
