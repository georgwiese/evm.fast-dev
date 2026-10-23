import InitECandidate.Solver.Mpt.DeleteUnwindIterationCost
import InitECandidate.Solver.Mpt.DeleteUnwindIteration
import InitECandidate.Solver.Mpt.DeleteUnwindRank
import InitECandidate.Solver.Mpt.DeleteUnwindSafety
import InitECandidate.Solver.Input.ClockCostCurrentLoop

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All outcomes of the original unwind loop from its real physical
stack rank. Only an actually continuing body must preserve its invariant;
errors, exceptions and timeouts require no future successful state. -/
theorem unwind_cost_ranked (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : UnwindModel source limit nodeLower pathLower property) :
    source.clock-(evaluateHOLFiniteState source unwind).2.clock≤(unwindAllowance pathLower+1)*unwindRank source := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>Nonempty (UnwindModel current limit nodeLower pathLower property)
  let rank:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>unwindRank current
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word : BitVec 64,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) unwindTest=some (.val (.word word))→word≠0→current.clock≠0→
      current.clock-1-(evaluateHOLFiniteState (decClockHOLFinite current) unwindBody).2.clock≤unwindAllowance pathLower := by
    intro current _code valid word observed nonzero _funded
    obtain ⟨model⟩:=valid
    change eval current unwindTest=some (.val (.word word)) at observed
    have active:=unwind_test_active current limit nodeLower pathLower property model word observed nonzero
    let entered:=model.with_clock current limit nodeLower pathLower property (current.clock-1)
    exact unwind_iteration_uniform_cost (decClockHOLFinite current) limit nodeLower pathLower property entered active
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word : BitVec 64,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) unwindTest=some (.val (.word word))→word≠0→
      0<rank current ∧ (current.clock≠0→let output:=evaluateHOLFiniteState (decClockHOLFinite current) unwindBody
        (output.1=none ∨ output.1=some .continue)→invariant output.2 ∧ rank output.2<rank current) := by
    intro current _code valid word observed nonzero
    obtain ⟨model⟩:=valid
    change eval current unwindTest=some (.val (.word word)) at observed
    have active:=unwind_test_active current limit nodeLower pathLower property model word observed nonzero
    have positive : 0<rank current:=by
      change 0<unwindRank current
      rw [unwind_rank_model current limit nodeLower pathLower property model]
      by_contra notPositive
      have empty : model.frames=[]:=List.length_eq_zero_iff.mp (by omega)
      exact active ((model.empty_iff current limit nodeLower pathLower property).1 empty)
    refine ⟨positive,?_⟩
    intro _funded
    dsimp only
    intro continuing
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) unwindBody
    have summary:=unwind_body_safe.summary_full (decClockHOLFinite current)
    unfold Input.LocalSummary at summary
    have normal : output.1=none:=by
      rcases continuing with normal|continued
      · exact normal
      · exact (summary.2.2.2 continued).elim
    have run : evaluateHOLFiniteState (decClockHOLFinite current) unwindBody=(none,output.2):=Prod.ext normal rfl
    let entered:=model.with_clock current limit nodeLower pathLower property (current.clock-1)
    obtain ⟨next,decreases,_grows,_members,_fields,_memory,_globals,_fresh,_protection⟩:=unwind_iteration_normal (decClockHOLFinite current) output.2 limit nodeLower pathLower property entered active run
    refine ⟨⟨next⟩,?_⟩
    change unwindRank output.2<unwindRank current
    rw [unwind_rank_model output.2 limit nodeLower pathLower property next,unwind_rank_model current limit nodeLower pathLower property model]
    change next.frames.length+1=model.frames.length at decreases
    omega
  rw [unwind_shapes.1]
  exact Input.ClockCost.ranked_loop_current source.code unwindTest unwindBody (unwindAllowance pathLower) invariant rank priced progress source rfl ⟨model⟩

/-- At most64 genuine saved key steps, including every stopped outcome.
This intermediate allowance counts source calls/loops, not target K. -/
theorem unwind_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : UnwindModel source limit nodeLower pathLower property) :
    source.clock-(evaluateHOLFiniteState source unwind).2.clock≤(unwindAllowance pathLower+1)*64 := by
  have rankBound : unwindRank source≤64:=by rw [unwind_rank_model source limit nodeLower pathLower property model]; exact model.bounded
  exact (unwind_cost_ranked source limit nodeLower pathLower property model).trans (Nat.mul_le_mul_left (unwindAllowance pathLower+1) rankBound)

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.unwind_cost_ranked
#print axioms InitECandidate.Solver.Mpt.DeleteBody.unwind_cost
