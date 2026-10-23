import InitECandidate.Solver.Mpt.IndexedIterationNormal
import InitECandidate.Solver.Input.ClockCostCurrentLoop

namespace InitECandidate.Solver.Mpt.Indexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def loopIndex (source : PanSemStateFiniteExact 64 Guest.HostMemory) : BitVec 64:=
  valueWord ((source.locals.lookup (ofString "i")).getD (.val (.word 0#64)))
def loopRank (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat) : Nat:=count-(loopIndex source).toNat

theorem loop_rank_model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m array : BitVec 64)
    (count cutoff limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop)
    (model : LoopModel source m array count cutoff limit slices property) : loopRank source count=count-model.index.toNat := by
  simp [loopRank,loopIndex,model.indexCell,valueWord]

theorem loop_test_active (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m array : BitVec 64)
    (count cutoff limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop)
    (model : LoopModel source m array count cutoff limit slices property) (word : BitVec 64)
    (read : eval source test=some (.val (.word word))) (nonzero : word≠0#64) : model.index.toNat<count := by
  have expected:=test_read source model.index count model.countBound model.indexCell model.countCell
  by_contra inactive
  rw [if_neg inactive] at expected
  have zero : word=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero zero

/-- The entire original indexed update loop, on every outcome. The rank
is the actual number of remaining input rows; only a real continuing
iteration supplies its next physical model and strict unsigned progress. -/
theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m array : BitVec 64)
    (count cutoff limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop)
    (model : LoopModel source m array count cutoff limit slices property) :
    source.clock-(evaluateHOLFiniteState source (.while test loopBody)).2.clock≤(SetTrie.bodyAllowance cutoff+21)*(count-model.index.toNat) := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>Nonempty (LoopModel current m array count cutoff limit slices property)
  let rank:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>loopRank current count
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word : BitVec 64,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word word))→word≠0→current.clock≠0→
      current.clock-1-(evaluateHOLFiniteState (decClockHOLFinite current) loopBody).2.clock≤SetTrie.bodyAllowance cutoff+20:=by
    intro current _code ⟨model⟩ word observed nonzero _funded
    have active:=loop_test_active current m array count cutoff limit slices property model word observed nonzero
    obtain ⟨entered,indexEq,_heapEq⟩:=model.dec_clock current m array count cutoff limit slices property
    exact iteration_cost (decClockHOLFinite current) m array count cutoff limit slices property entered (by rw [indexEq]; exact active)
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word : BitVec 64,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word word))→word≠0→
      0<rank current ∧ (current.clock≠0→let output:=evaluateHOLFiniteState (decClockHOLFinite current) loopBody
        (output.1=none ∨ output.1=some .continue)→invariant output.2 ∧ rank output.2<rank current):=by
    intro current _code ⟨model⟩ word observed nonzero
    have active:=loop_test_active current m array count cutoff limit slices property model word observed nonzero
    have rankEq:=loop_rank_model current m array count cutoff limit slices property model
    refine ⟨by change 0<loopRank current count; rw [rankEq]; omega,?_⟩
    intro _funded
    dsimp only
    intro continuing
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) loopBody
    have summary:=loop_body_limit.summary_full (decClockHOLFinite current)
    unfold Input.LocalSummary at summary
    have normal : output.1=none:=by
      rcases continuing with normal|continued
      · exact normal
      · exact (summary.2.2.2 continued).elim
    have run : evaluateHOLFiniteState (decClockHOLFinite current) loopBody=(none,output.2):=Prod.ext normal rfl
    obtain ⟨entered,indexEq,_heapEq⟩:=model.dec_clock current m array count cutoff limit slices property
    obtain ⟨next,advance,_grows,_memory⟩:=iteration_normal (decClockHOLFinite current) output.2 m array count cutoff limit slices property entered (by rw [indexEq]; exact active) run
    have number : (model.index+1#64).toNat=model.index.toNat+1:=by
      rw [BitVec.toNat_add_of_lt (by change model.index.toNat+1<2^64; have bounded:=model.countBound; omega)]; rfl
    have nextRank:=loop_rank_model output.2 m array count cutoff limit slices property next
    refine ⟨⟨next⟩,?_⟩
    change loopRank output.2 count<loopRank current count
    rw [nextRank,advance,indexEq,number,rankEq]
    omega
  have price:=Input.ClockCost.ranked_loop_current source.code test loopBody (SetTrie.bodyAllowance cutoff+20) invariant rank priced progress source rfl ⟨model⟩
  change source.clock-(evaluateHOLFiniteState source (.while test loopBody)).2.clock≤(SetTrie.bodyAllowance cutoff+20+1)*loopRank source count at price
  rwa [loop_rank_model source m array count cutoff limit slices property model] at price

end InitECandidate.Solver.Mpt.Indexed

#print axioms InitECandidate.Solver.Mpt.Indexed.loop_rank_model
#print axioms InitECandidate.Solver.Mpt.Indexed.loop_test_active
#print axioms InitECandidate.Solver.Mpt.Indexed.loop_cost
