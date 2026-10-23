import InitECandidate.Solver.Mpt.DeleteDescentOutput

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Analysis rank read from the actual original scalar locals. It does
not run in the guest and assigns no order to trie child pointers. -/
def descentRank (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat:=
  let go:=valueWord ((source.locals.lookup (ofString "go")).getD (.val (.word 0#64)))
  let level:=valueWord ((source.locals.lookup (ofString "level")).getD (.val (.word 0#64)))
  let length:=valueWord ((source.locals.lookup (ofString "klen")).getD (.val (.word 0#64)))
  if go=0#64 then 0 else length.toNat-level.toNat+1

theorem descent_rank_model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) :
    descentRank source=if model.go=0#64 then 0 else length.toNat-model.level.toNat+1 := by
  simp only [descentRank,model.goCell,model.levelCell,model.lengthCell,Option.getD_some,valueWord]

theorem descent_rank_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) : descentRank source≤65 := by
  rw [descent_rank_model source key length limit nodeLower pathLower property model]
  split
  · omega
  · have bounded:=model.bounded; omega

theorem descent_test_active (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (word : BitVec 64)
    (read : QueryBranch.eval source descentTest=some (.val (.word word))) (nonzero : word≠0#64) : model.go≠0#64 := by
  intro stopped
  have expected : QueryBranch.eval source descentTest=some (.val (.word 0#64)):=by
    simp [QueryBranch.eval,descentTest,QueryBranch.localVar,evalHOLExact,toExact,model.goCell,stopped,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have zero : word=0#64:=by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero zero

theorem descent_rank_decreases (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.go≠0#64)
    (output : DescentOutput source target key length limit nodeLower pathLower property model) : descentRank target<descentRank source := by
  rw [descent_rank_model target key length limit nodeLower pathLower property output.next,descent_rank_model source key length limit nodeLower pathLower property model,if_neg active]
  by_cases stopped : output.next.go=0#64
  · rw [if_pos stopped]; omega
  · rw [if_neg stopped]
    have progress : model.level.toNat<output.next.level.toNat:=by
      rcases output.progress with terminal|increases
      · exact (stopped terminal).elim
      · exact increases
    have before:=output.next.levelBound
    omega

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_rank_model
#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_rank_bound
#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_test_active
#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_rank_decreases
