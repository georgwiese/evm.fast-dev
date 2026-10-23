import InitECandidate.Solver.Mpt.DeleteUnwindModel

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Read the actual physical PREV chain, using one more than the maximum
number of genuine saved key steps. This analysis function never runs in
the guest and does not assume a rank on trie child pointers. -/
def stackDepth : Nat→Memory→BitVec 64→Nat
  | 0,_,_=>0
  | fuel+1,memory,top=>if top=0#64 then 0 else stackDepth fuel memory (wordAt memory top)+1

theorem stack_depth_count (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (top : BitVec 64)
    (frames : List DeleteFrame.Saved) (stack : DeleteFrame.Stack source cursor top frames)
    (fuel : Nat) (enough : frames.length≤fuel) : stackDepth fuel source.memory top=frames.length := by
  induction frames generalizing top fuel with
  | nil=>
    have zero : top=0#64:=stack
    subst top
    cases fuel <;> simp [stackDepth]
  | cons saved tail ih=>
    obtain ⟨topEq,_above,view,rest⟩:=stack
    have active : top≠0#64:=by rw [topEq]; exact view.nonzero source saved
    have previous : wordAt source.memory top=saved.previous:=by
      rw [topEq]
      simp [wordAt,view.previous_cell source saved,MemoryBytes.wordBits]
    cases fuel with
    | zero=>simp at enough
    | succ fuel=>
      rw [stackDepth,if_neg active,previous,ih saved.previous rest fuel (by simp only [List.length_cons] at enough; omega)]
      rfl

def unwindRank (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat:=
  stackDepth 65 source.memory (valueWord ((source.locals.lookup (ofString "top")).getD (.val (.word 0#64))))

theorem unwind_rank_model (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : UnwindModel source limit nodeLower pathLower property) : unwindRank source=model.frames.length := by
  simp only [unwindRank,model.topCell,Option.getD_some,valueWord]
  exact stack_depth_count source model.cursor.toNat model.top model.frames model.stack 65 (by have small:=model.bounded; omega)

theorem unwind_test_active (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : UnwindModel source limit nodeLower pathLower property) (word : BitVec 64)
    (read : QueryBranch.eval source unwindTest=some (.val (.word word))) (nonzero : word≠0#64) : model.top≠0#64 := by
  intro stopped
  have expected : QueryBranch.eval source unwindTest=some (.val (.word 0#64)):=by
    simp [QueryBranch.eval,unwindTest,QueryBranch.localVar,evalHOLExact,toExact,model.topCell,stopped,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have zero : word=0#64:=by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero zero

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.stack_depth_count
#print axioms InitECandidate.Solver.Mpt.DeleteBody.unwind_rank_model
#print axioms InitECandidate.Solver.Mpt.DeleteBody.unwind_test_active
