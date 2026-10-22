import InitECandidate.Solver.Input.GuardedCounter
import InitECandidate.Solver.Input.CounterLoopCost
import InitECandidate.Solver.Input.LoopInvariantNoControl

namespace InitECandidate.Solver.Input.SignedGuardedCounterLoop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def Invariant (limit : MlS) (length : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ word, source.locals.lookup (ofString "i")=some (.val (.word word)) ∧
    source.locals.lookup limit=some (.val (.word (BitVec.ofNat 64 length))) ∧ word.toNat≤length

def rank (length : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  length-(CounterFlow.counterWord source (ofString "i")).toNat

/-- The original signed comparison is unsigned only because the actual
counter and decoded length both remain below the signed boundary. -/
theorem test_read (limit : MlS) (length : Nat) (small : length<2^63)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (counter : source.locals.lookup (ofString "i")=some (.val (.word word)))
    (count : source.locals.lookup limit=some (.val (.word (BitVec.ofNat 64 length))))
    (bounded : word.toNat≤length) :
    evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address))
      (.cmp .less (localVar "i") (.var .local limit))=
      some (.val (.word (if word.toNat<length then 1#64 else 0#64))) := by
  have number : (BitVec.ofNat 64 length).toNat=length := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have counterSmall : word.toNat<9223372036854775808 := by omega
  simp [evalHOLFinite,evalHOLExact,toExact,localVar,counter,count,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,
    number,counterSmall,show length<9223372036854775808 from small]

theorem transition (limit : MlS) (body : ProgHOL 64) (length : Nat)
    (other : limit≠ofString "i") (small : length<2^63) (guarded : GuardedCounter 1 body)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : Invariant limit length source) (observed : BitVec 64)
    (read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address))
      (.cmp .less (localVar "i") (.var .local limit))=some (.val (.word observed)))
    (nonzero : observed≠0#64) : 0<rank length source ∧
      (source.clock≠0 → let output:=evaluateHOLFiniteState (decClockHOLFinite source) body
        (output.1=none ∨ output.1=some .continue) →
          Invariant limit length output.2 ∧ rank length output.2<rank length source) := by
  obtain ⟨word,counter,count,bounded⟩:=valid
  have expected:=test_read limit length small source word counter count bounded
  have active : word.toNat<length := by
    by_contra inactive
    rw [if_neg inactive] at expected
    have zero : observed=0#64 := by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
    exact nonzero zero
  have rankEq : rank length source=length-word.toNat := by
    simp [rank,CounterFlow.counterWord,counter,valueWord]
  refine ⟨by rw [rankEq]; omega,?_⟩
  intro funded
  dsimp only
  intro continuing
  let output:=evaluateHOLFiniteState (decClockHOLFinite source) body
  have normal : output.1=none := continuing.resolve_right (guarded.no_control (decClockHOLFinite source)).2
  have run : evaluateHOLFiniteState (decClockHOLFinite source) body=(none,output.2) := Prod.ext normal rfl
  have postEq:=guarded.normal (decClockHOLFinite source) output.2 word counter run
  have number : (word+1#64).toNat=word.toNat+1 := by
    rw [BitVec.toNat_add_of_lt (by change word.toNat+1<2^64; omega)]
    rfl
  have nextCell : output.2.locals.lookup (ofString "i")=some (.val (.word (word+1#64))) := by
    rw [postEq]; exact bind_lookup_same _ _ _
  have nextCount : output.2.locals.lookup limit=some (.val (.word (BitVec.ofNat 64 length))) := by
    rw [postEq]
    simpa [WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm other,decClockHOLFinite] using count
  have nextRank : rank length output.2=length-(word.toNat+1) := by
    simp [rank,CounterFlow.counterWord,nextCell,valueWord,number]
  exact ⟨⟨word+1#64,nextCell,nextCount,by rw [number]; omega⟩,by rw [nextRank,rankEq]; omega⟩

/-- Every outcome of the actual guarded loop costs at most its remaining
decoded count. A failed read or exception needs no continuing invariant. -/
theorem cost (limit : MlS) (body : ProgHOL 64) (length : Nat)
    (other : limit≠ofString "i") (small : length<2^63) (guarded : GuardedCounter 1 body)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : Invariant limit length source) :
    source.clock-(evaluateHOLFiniteState source (.while (.cmp .less (localVar "i") (.var .local limit)) body)).2.clock≤rank length source := by
  have priced:=ClockCost.ranked_loop source.code _ body 0 (Invariant limit length) (rank length)
    (ClockCost.of_quiet source.code body (guarded.quiet source.code))
    (by intro current codeEq ready observed read nonzero
        exact transition limit body length other small guarded current ready observed read nonzero) source rfl valid
  simpa only [Nat.zero_add,Nat.one_mul] using priced

theorem normal (limit : MlS) (body : ProgHOL 64) (length : Nat)
    (other : limit≠ofString "i") (small : length<2^63) (guarded : GuardedCounter 1 body)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : Invariant limit length source)
    (run : evaluateHOLFiniteState source (.while (.cmp .less (localVar "i") (.var .local limit)) body)=(none,post)) :
    Invariant limit length post := by
  apply loop_invariant_no_control source.code _ body guarded.no_control (Invariant limit length) _ source post rfl valid run
  intro current codeEq ready observed read nonzero funded target bodyRun
  have info:=(transition limit body length other small guarded current ready observed read nonzero).2 funded
  rw [bodyRun] at info
  exact (info (Or.inl rfl)).1

end InitECandidate.Solver.Input.SignedGuardedCounterLoop

#print axioms InitECandidate.Solver.Input.SignedGuardedCounterLoop.test_read
#print axioms InitECandidate.Solver.Input.SignedGuardedCounterLoop.transition
#print axioms InitECandidate.Solver.Input.SignedGuardedCounterLoop.cost
#print axioms InitECandidate.Solver.Input.SignedGuardedCounterLoop.normal
