import InitECandidate.Solver.Input.CounterLoopCost
import InitECandidate.Solver.Input.LoopInvariantNoControl

namespace InitECandidate.Solver.Input.CounterFlow
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def StrideInvariant (length : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ word,source.locals.lookup (ofString "i")=some (.val (.word word)) ∧
    source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))) ∧ word.toNat≤length
def StrideReads (test : ExpHOL 64) (stride length : Nat) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,∀ word : BitVec 64,
    source.locals.lookup (ofString "i")=some (.val (.word word))→
    source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))→word.toNat≤length→
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=
      some (.val (.word (if word.toNat+stride≤length then 1#64 else 0#64)))
def strideRank (stride length : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat:=
  (length-(counterWord source (ofString "i")).toNat)/stride

-- One checked stride argument for an actual named length local.
-- The existing n-based public interface remains a specialization below.
namespace NamedStride

def Invariant (limit : MlS) (length : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ word,source.locals.lookup (ofString "i")=some (.val (.word word)) ∧
    source.locals.lookup limit=some (.val (.word (BitVec.ofNat 64 length))) ∧ word.toNat≤length
def Reads (limit : MlS) (test : ExpHOL 64) (stride length : Nat) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,∀ word : BitVec 64,
    source.locals.lookup (ofString "i")=some (.val (.word word))→
    source.locals.lookup limit=some (.val (.word (BitVec.ofNat 64 length)))→word.toNat≤length→
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=
      some (.val (.word (if word.toNat+stride≤length then 1#64 else 0#64)))

theorem transition (limit : MlS) (test : ExpHOL 64) (body : ProgHOL 64) (stride length : Nat)
    (positive : 0<stride) (small : length<2^64) (advance : Advances (ofString "i") stride body)
    (summary : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary limit body source)
    (testReads : Reads limit test stride length) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (valid : Invariant limit length source) (observed : BitVec 64)
    (read : evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=some (.val (.word observed)))
    (nonzero : observed≠0#64) : 0<strideRank stride length source ∧
      (source.clock≠0→let output:=evaluateHOLFiniteState (decClockHOLFinite source) body;
        (output.1=none ∨ output.1=some .continue)→Invariant limit length output.2 ∧ strideRank stride length output.2<strideRank stride length source) := by
  obtain ⟨word,cell,nCell,bounded⟩:=valid
  have expected:=testReads source word cell nCell bounded
  have active : word.toNat+stride≤length:=by
    by_cases active : word.toNat + stride ≤ length
    · exact active
    have inactive := active
    rw [if_neg inactive] at expected
    have zero : observed=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
    exact False.elim (nonzero zero)
  have rankEq : strideRank stride length source=(length-word.toNat)/stride:=by simp [strideRank,counterWord,cell,valueWord]
  refine ⟨by rw [rankEq]; exact Nat.div_pos (by omega) positive,?_⟩
  intro funded
  dsimp only
  intro continuing
  let output:=evaluateHOLFiniteState (decClockHOLFinite source) body
  have info:=summary (decClockHOLFinite source)
  unfold LocalSummary at info
  have normal : output.1=none:=continuing.resolve_right info.2.2.2
  have run : evaluateHOLFiniteState (decClockHOLFinite source) body=(none,output.2):=Prod.ext normal rfl
  have nextCell:=advance (decClockHOLFinite source) output.2 word cell run
  have nextN : output.2.locals.lookup limit=some (.val (.word (BitVec.ofNat 64 length))):=(info.1 normal).trans nCell
  have strideSmall : stride<2^64:=by omega
  have number : (word+BitVec.ofNat 64 stride).toNat=word.toNat+stride:=by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt strideSmall]; omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt strideSmall]
  have nextRank : strideRank stride length output.2=(length-(word.toNat+stride))/stride:=by simp [strideRank,counterWord,nextCell,valueWord,number]
  have difference : length-word.toNat=(length-(word.toNat+stride))+stride:=by omega
  have decrease : (length-(word.toNat+stride))/stride<(length-word.toNat)/stride:=by rw [difference,Nat.add_div_right _ positive]; omega
  exact ⟨⟨word+BitVec.ofNat 64 stride,nextCell,nextN,by rw [number]; exact active⟩,by rw [nextRank,rankEq]; exact decrease⟩

theorem loop_cost (limit : MlS) (code) (test : ExpHOL 64) (body : ProgHOL 64) (stride length price : Nat)
    (positive : 0<stride) (small : length<2^64) (advance : Advances (ofString "i") stride body)
    (summary : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary limit body source)
    (testReads : Reads limit test stride length) (priced : ClockCost.Bound code body price)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : source.code=code) (valid : Invariant limit length source) :
    source.clock-(evaluateHOLFiniteState source (.while test body)).2.clock≤(price+1)*strideRank stride length source :=
  ClockCost.ranked_loop code test body price (Invariant limit length) (strideRank stride length) priced
    (by intro current codeEq ready observed read nonzero; exact transition limit test body stride length positive small advance summary testReads current ready observed read nonzero)
    source installed valid

theorem loop_normal (limit : MlS) (code) (test : ExpHOL 64) (body : ProgHOL 64) (stride length : Nat)
    (positive : 0<stride) (small : length<2^64) (advance : Advances (ofString "i") stride body)
    (summary : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary limit body source)
    (testReads : Reads limit test stride length) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : source.code=code) (valid : Invariant limit length source)
    (normal : evaluateHOLFiniteState source (.while test body)=(none,target)) : Invariant limit length target := by
  apply loop_invariant_no_control code test body (fun current=>(summary current).2.2) (Invariant limit length) _ source target installed valid normal
  intro current codeEq ready observed read nonzero funded post bodyRun
  have transition:=(transition limit test body stride length positive small advance summary testReads current ready observed read nonzero).2 funded
  rw [bodyRun] at transition
  exact (transition (Or.inl rfl)).1

end NamedStride

theorem stride_transition (test : ExpHOL 64) (body : ProgHOL 64) (stride length : Nat)
    (positive : 0<stride) (small : length<2^64) (advance : Advances (ofString "i") stride body)
    (summary : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary (ofString "n") body source)
    (testReads : StrideReads test stride length) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (valid : StrideInvariant length source) (observed : BitVec 64)
    (read : evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=some (.val (.word observed)))
    (nonzero : observed≠0#64) : 0<strideRank stride length source ∧
      (source.clock≠0→let output:=evaluateHOLFiniteState (decClockHOLFinite source) body;
        (output.1=none ∨ output.1=some .continue)→StrideInvariant length output.2 ∧ strideRank stride length output.2<strideRank stride length source) := by
  exact NamedStride.transition (ofString "n") test body stride length positive small advance summary testReads source valid observed read nonzero
theorem stride_loop_cost (code) (test : ExpHOL 64) (body : ProgHOL 64) (stride length price : Nat)
    (positive : 0<stride) (small : length<2^64) (advance : Advances (ofString "i") stride body)
    (summary : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary (ofString "n") body source)
    (testReads : StrideReads test stride length) (priced : ClockCost.Bound code body price)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : source.code=code) (valid : StrideInvariant length source) :
    source.clock-(evaluateHOLFiniteState source (.while test body)).2.clock≤(price+1)*strideRank stride length source := by
  exact NamedStride.loop_cost (ofString "n") code test body stride length price positive small advance summary testReads priced source installed valid

theorem stride_loop_normal (code) (test : ExpHOL 64) (body : ProgHOL 64) (stride length : Nat)
    (positive : 0<stride) (small : length<2^64) (advance : Advances (ofString "i") stride body)
    (summary : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary (ofString "n") body source)
    (testReads : StrideReads test stride length) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : source.code=code) (valid : StrideInvariant length source)
    (normal : evaluateHOLFiniteState source (.while test body)=(none,target)) : StrideInvariant length target := by
  exact NamedStride.loop_normal (ofString "n") code test body stride length positive small advance summary testReads source target installed valid normal

end InitECandidate.Solver.Input.CounterFlow

#print axioms InitECandidate.Solver.Input.CounterFlow.stride_transition
#print axioms InitECandidate.Solver.Input.CounterFlow.stride_loop_cost
#print axioms InitECandidate.Solver.Input.CounterFlow.stride_loop_normal

#print axioms InitECandidate.Solver.Input.CounterFlow.NamedStride.transition
#print axioms InitECandidate.Solver.Input.CounterFlow.NamedStride.loop_cost
#print axioms InitECandidate.Solver.Input.CounterFlow.NamedStride.loop_normal
