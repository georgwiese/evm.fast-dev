import InitECandidate.Solver.Mpt.InsertIterationCost
import InitECandidate.Solver.Mpt.InsertIterationNormal
import InitECandidate.Solver.Input.ClockCostCurrentLoop

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def loopWord (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) : BitVec 64:=
  valueWord ((source.locals.lookup (ofString name)).getD (.val (.word 0#64)))

def loopRank (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64) : Nat:=
  if loopWord source "go"=0#64 then 0 else length.toNat-(loopWord source "level").toNat+1

theorem loop_rank_model (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (key length pointer size : BitVec 64) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (model : LoopModel source key length pointer size limit nodeLower pathLower property) :
    loopRank source length=if model.go=0#64 then 0 else length.toNat-model.level.toNat+1 := by
  simp [loopRank,loopWord,model.goCell,model.levelCell,valueWord]

theorem loop_test_active (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (key length pointer size : BitVec 64) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (model : LoopModel source key length pointer size limit nodeLower pathLower property) (word : BitVec 64)
    (read : eval source test=some (.val (.word word))) (nonzero : word≠0#64) : model.go≠0#64 := by
  intro stopped
  have expected : eval source test=some (.val (.word 0#64)):=by
    simp [eval,test,localVar,evalHOLExact,toExact,model.goCell,stopped,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have zero : word=0#64:=by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero zero

/-- All loop outcomes, priced from the actual current key rank. A normal
continued iteration strictly consumes key nibbles; stopped, failing and
timeout iterations do not require any future successful graph state. -/
theorem loop_cost_ranked (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (key length pointer size : BitVec 64) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (model : LoopModel source key length pointer size limit nodeLower pathLower property)
    (extra : property pointer size) (empty : property 0#64 0#64) :
    source.clock-(evaluateHOLFiniteState source (.while test loopBody)).2.clock≤566*loopRank source length := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>Nonempty (LoopModel current key length pointer size limit nodeLower pathLower property)
  let rank:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>loopRank current length
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word word)) → word≠0 → current.clock≠0 →
      current.clock-1-(evaluateHOLFiniteState (decClockHOLFinite current) loopBody).2.clock≤565 := by
    intro current _code valid word observed nonzero _funded
    obtain ⟨model⟩:=valid
    change eval current test=some (.val (.word word)) at observed
    have active:=loop_test_active current key length pointer size limit nodeLower pathLower property model word observed nonzero
    have inputs : ScalarInputs (decClockHOLFinite current) model.node key model.level length pointer size:=
      ⟨model.nodeCell,model.keyCell,model.levelCell,model.lengthCell,model.pointerCell,model.sizeCell⟩
    exact iteration_cost (decClockHOLFinite current) model.node key model.level length pointer size model.go inputs model.bounded
      (model.activeBound active) model.installed model.goCell
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word word)) → word≠0 →
      0<rank current ∧ (current.clock≠0 → let output:=evaluateHOLFiniteState (decClockHOLFinite current) loopBody
        (output.1=none ∨ output.1=some .continue) → invariant output.2 ∧ rank output.2<rank current) := by
    intro current _code valid word observed nonzero
    obtain ⟨model⟩:=valid
    change eval current test=some (.val (.word word)) at observed
    have active:=loop_test_active current key length pointer size limit nodeLower pathLower property model word observed nonzero
    have rankEq:=loop_rank_model current key length pointer size limit nodeLower pathLower property model
    have positive : 0<rank current:=by change 0<loopRank current length; rw [rankEq,if_neg active]; omega
    refine ⟨positive,?_⟩
    intro _funded
    dsimp only
    intro continuing
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) loopBody
    have summary:=loop_body_safe.summary_full (decClockHOLFinite current)
    unfold Input.LocalSummary at summary
    have normal : output.1=none:=by
      rcases continuing with normal|continued
      · exact normal
      · exact (summary.2.2.2 continued).elim
    have run : evaluateHOLFiniteState (decClockHOLFinite current) loopBody=(none,output.2):=Prod.ext normal rfl
    let entered : LoopModel (decClockHOLFinite current) key length pointer size limit nodeLower pathLower property:={model with}
    obtain ⟨next,_grows,_members,_memory,_tags,advance,_fields,_protectedWords,_activeRegistry,_provenance,_protection,_positive,_kind⟩:=iteration_path_normal (decClockHOLFinite current) output.2 key length pointer size limit nodeLower pathLower property entered active extra empty run
    have nextRank:=loop_rank_model output.2 key length pointer size limit nodeLower pathLower property next
    refine ⟨⟨next⟩,?_⟩
    change loopRank output.2 length<loopRank current length
    by_cases stopped : next.go=0#64
    · rw [nextRank,if_pos stopped]
      exact positive
    · have strict : model.level.toNat<next.level.toNat:=advance.elim (fun zero=>(stopped zero).elim) id
      have before:=model.activeBound active
      have after:=next.activeBound stopped
      rw [nextRank,if_neg stopped,rankEq,if_neg active]
      omega
  exact Input.ClockCost.ranked_loop_current source.code test loopBody 565 invariant rank priced progress source rfl ⟨model⟩

/-- At most65 ranked iterations of the original insertion loop, including
all failing and timeout outcomes. This is a source-clock allowance only. -/
theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (key length pointer size : BitVec 64) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (model : LoopModel source key length pointer size limit nodeLower pathLower property)
    (extra : property pointer size) (empty : property 0#64 0#64) :
    source.clock-(evaluateHOLFiniteState source (.while test loopBody)).2.clock≤36790 := by
  have rankBound : loopRank source length≤65:=by
    rw [loop_rank_model source key length pointer size limit nodeLower pathLower property model]
    have bounded:=model.bounded
    split <;> omega
  exact (loop_cost_ranked source key length pointer size limit nodeLower pathLower property model extra empty).trans (Nat.mul_le_mul_left 566 rankBound)

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.loop_rank_model
#print axioms InitECandidate.Solver.Mpt.Insert.loop_test_active
#print axioms InitECandidate.Solver.Mpt.Insert.loop_cost_ranked
#print axioms InitECandidate.Solver.Mpt.Insert.loop_cost
