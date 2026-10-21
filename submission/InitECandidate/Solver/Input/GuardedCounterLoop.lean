import InitECandidate.Solver.Input.GuardedCounter
import InitECandidate.Solver.Input.CounterLoopCost
import InitECandidate.Solver.Input.LoopInvariantNoControl

namespace InitECandidate.Solver.Input.GuardedCounterLoop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def Invariant (length : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ word,source.locals.lookup (ofString "i")=some (.val (.word word)) ∧
    source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))) ∧ word.toNat≤length

def TestReads (test : ExpHOL 64) (stride length : Nat) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,∀ word : BitVec 64,
    source.locals.lookup (ofString "i")=some (.val (.word word)) →
    source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))) → word.toNat≤length →
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=
      some (.val (.word (if word.toNat+stride≤length then 1#64 else 0#64)))

def rank (length : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) := length-(CounterFlow.counterWord source (ofString "i")).toNat

theorem transition (test : ExpHOL 64) (body : ProgHOL 64) (stride length : Nat)
    (positive : 0<stride) (small : length≤64) (guarded : Input.GuardedCounter stride body) (testReads : TestReads test stride length)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : Invariant length source) (observed : BitVec 64)
    (read : evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=some (.val (.word observed)))
    (nonzero : observed≠0#64) : 0<rank length source ∧
      (source.clock≠0 → let output:=evaluateHOLFiniteState (decClockHOLFinite source) body;
        (output.1=none ∨ output.1=some .continue) → Invariant length output.2 ∧ rank length output.2<rank length source) := by
  obtain ⟨word,cell,nCell,bounded⟩ := valid
  have expected:=testReads source word cell nCell bounded
  have active : word.toNat+stride≤length := by
    by_contra inactive
    rw [if_neg inactive] at expected
    have zero : observed=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
    exact nonzero zero
  have rankEq : rank length source=length-word.toNat := by simp [rank,CounterFlow.counterWord,cell,valueWord]
  refine ⟨by rw [rankEq]; omega,?_⟩
  intro funded
  dsimp only
  intro continuing
  let output:=evaluateHOLFiniteState (decClockHOLFinite source) body
  have normal : output.1=none := continuing.resolve_right (guarded.no_control (decClockHOLFinite source)).2
  have run : evaluateHOLFiniteState (decClockHOLFinite source) body=(none,output.2) := Prod.ext normal rfl
  have postEq:=guarded.normal (decClockHOLFinite source) output.2 word cell run
  have stepSmall : stride<2^64 := by omega
  have number : (word+BitVec.ofNat 64 stride).toNat=word.toNat+stride := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt stepSmall]; omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt stepSmall]
  have nextCell : output.2.locals.lookup (ofString "i")=some (.val (.word (word+BitVec.ofNat 64 stride))) := by rw [postEq]; exact bind_lookup_same _ _ _
  have nextN : output.2.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))) := by
    rw [postEq]
    exact (bind_lookup_other _ "i" "n" _ (by decide)).trans nCell
  have nextRank : rank length output.2=length-(word.toNat+stride) := by simp [rank,CounterFlow.counterWord,nextCell,valueWord,number]
  exact ⟨⟨word+BitVec.ofNat 64 stride,nextCell,nextN,by rw [number]; exact active⟩,by rw [nextRank,rankEq]; omega⟩

theorem cost (test : ExpHOL 64) (body : ProgHOL 64) (stride length : Nat)
    (positive : 0<stride) (small : length≤64) (guarded : Input.GuardedCounter stride body) (testReads : TestReads test stride length)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : Invariant length source) :
    source.clock-(evaluateHOLFiniteState source (.while test body)).2.clock≤length := by
  have price:=ClockCost.ranked_loop source.code test body 0 (Invariant length) (rank length)
    (ClockCost.of_quiet source.code body (guarded.quiet source.code))
    (by intro current codeEq ready observed read nonzero; exact transition test body stride length positive small guarded testReads current ready observed read nonzero) source rfl valid
  simp only [Nat.zero_add,Nat.one_mul] at price
  exact price.trans (Nat.sub_le _ _)

theorem normal (test : ExpHOL 64) (body : ProgHOL 64) (stride length : Nat)
    (positive : 0<stride) (small : length≤64) (guarded : Input.GuardedCounter stride body) (testReads : TestReads test stride length)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : Invariant length source)
    (run : evaluateHOLFiniteState source (.while test body)=(none,post)) : Invariant length post := by
  apply loop_invariant_no_control source.code test body guarded.no_control (Invariant length) _ source post rfl valid run
  intro current codeEq ready observed read nonzero funded target bodyRun
  have info:=(transition test body stride length positive small guarded testReads current ready observed read nonzero).2 funded
  rw [bodyRun] at info
  exact (info (Or.inl rfl)).1

end InitECandidate.Solver.Input.GuardedCounterLoop

#print axioms InitECandidate.Solver.Input.GuardedCounterLoop.transition
#print axioms InitECandidate.Solver.Input.GuardedCounterLoop.cost
#print axioms InitECandidate.Solver.Input.GuardedCounterLoop.normal
