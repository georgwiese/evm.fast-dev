import InitECandidate.Solver.Mpt.DeleteDescentIterationCost
import InitECandidate.Solver.Mpt.DeleteDescentIteration
import InitECandidate.Solver.Mpt.DeleteDescentRank
import InitECandidate.Solver.Mpt.DeleteDescentSafety
import InitECandidate.Solver.Input.ClockCostCurrentLoop

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every outcome of the actual original descent loop, including errors,
exceptions and timeouts. Only genuinely continuing iterations derive
their next physical model and strictly decrease the actual scalar rank. -/
theorem descent_cost_ranked (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (empty : property 0#64 0#64) :
    source.clock-(evaluateHOLFiniteState source descent).2.clock≤(descentAllowance pathLower+1)*descentRank source := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>Nonempty (DescentModel current key length limit nodeLower pathLower property)
  let rank:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>descentRank current
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word : BitVec 64,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) descentTest=some (.val (.word word))→word≠0→current.clock≠0→
      current.clock-1-(evaluateHOLFiniteState (decClockHOLFinite current) descentBody).2.clock≤descentAllowance pathLower := by
    intro current _code valid _word _observed _nonzero _funded
    obtain ⟨model⟩:=valid
    let entered:=model.with_clock current key length limit nodeLower pathLower property (current.clock-1)
    exact descent_iteration_uniform_cost (decClockHOLFinite current) key length limit nodeLower pathLower property entered empty
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word : BitVec 64,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) descentTest=some (.val (.word word))→word≠0→
      0<rank current ∧ (current.clock≠0→let output:=evaluateHOLFiniteState (decClockHOLFinite current) descentBody
        (output.1=none ∨ output.1=some .continue)→invariant output.2 ∧ rank output.2<rank current) := by
    intro current _code valid word observed nonzero
    obtain ⟨model⟩:=valid
    change eval current descentTest=some (.val (.word word)) at observed
    have active:=descent_test_active current key length limit nodeLower pathLower property model word observed nonzero
    have positive : 0<rank current:=by
      change 0<descentRank current
      rw [descent_rank_model current key length limit nodeLower pathLower property model,if_neg active]
      omega
    refine ⟨positive,?_⟩
    intro _funded
    dsimp only
    intro continuing
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) descentBody
    have summary:=descent_body_safe.summary_full (decClockHOLFinite current)
    unfold Input.LocalSummary at summary
    have normal : output.1=none:=by
      rcases continuing with normal|continued
      · exact normal
      · exact (summary.2.2.2 continued).elim
    have run : evaluateHOLFiniteState (decClockHOLFinite current) descentBody=(none,output.2):=Prod.ext normal rfl
    let entered:=model.with_clock current key length limit nodeLower pathLower property (current.clock-1)
    obtain ⟨result⟩:=descent_iteration_normal (decClockHOLFinite current) output.2 key length limit nodeLower pathLower property entered empty run
    exact ⟨⟨result.next⟩,descent_rank_decreases (decClockHOLFinite current) output.2 key length limit nodeLower pathLower property entered active result⟩
  rw [descent_shapes.1]
  exact Input.ClockCost.ranked_loop_current source.code descentTest descentBody (descentAllowance pathLower) invariant rank priced progress source rfl ⟨model⟩

/-- At most65 genuine key-progress iterations, including every aborted
outcome. This is a local source allowance, not the final target bound. -/
theorem descent_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (empty : property 0#64 0#64) :
    source.clock-(evaluateHOLFiniteState source descent).2.clock≤(descentAllowance pathLower+1)*65 :=
  (descent_cost_ranked source key length limit nodeLower pathLower property model empty).trans
    (Nat.mul_le_mul_left (descentAllowance pathLower+1) (descent_rank_bound source key length limit nodeLower pathLower property model))

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_cost_ranked
#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_cost
