import InitECandidate.Solver.Input.CounterLoopCost
import InitECandidate.Solver.Input.ZeroByteFlow
import InitECandidate.Solver.Input.LoopSummaryInvariant
import InitECandidate.Solver.Input.ClockCostCurrentLoop

namespace InitECandidate.Solver.Input.ZeroShort
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def valid (length : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ index : Nat,index≤length ∧ source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) ∧
    source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))
def rank (length : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) := length-(CounterFlow.counterWord source (ofString "i")).toNat

/-- Current counter facts for the original byte8/tail1 loops. No mapped
memory or successful store is assumed: failed stores stop within their tick. -/
structure Model (code) (test : ExpHOL 64) (body : ProgHOL 64) (stride length : Nat) : Prop where
  positive : 0<stride
  short : length<32
  read : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,∀ index,index≤length →
    source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) →
    source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))) →
    evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) test=some (.val (.word (if index+stride≤length then 1#64 else 0#64)))
  advance : CounterFlow.Advances (ofString "i") stride body
  summary : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary (ofString "n") body source
  quiet : QuietClock.Preserves code body

private theorem Model.progress (code) (test : ExpHOL 64) (body : ProgHOL 64) (stride length : Nat) (model : Model code test body stride length)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ready : valid length source) (word : BitVec 64)
    (read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) test=some (.val (.word word))) (nonzero : word≠0) :
    0<rank length source ∧ (source.clock≠0 → let output:=evaluateHOLFiniteState (decClockHOLFinite source) body
      (output.1=none ∨ output.1=some .continue) → valid length output.2 ∧ rank length output.2<rank length source) := by
  obtain ⟨index,inside,indexLocal,lengthLocal⟩ := ready
  have expected := model.read source index inside indexLocal lengthLocal
  have active : index+stride≤length := by
    by_contra inactive
    rw [if_neg inactive] at expected
    have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
    exact nonzero zero
  have number : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have h:=model.short; omega)]
  have rankEq : rank length source=length-index := by simp [rank,CounterFlow.counterWord,indexLocal,valueWord,number]
  refine ⟨by rw [rankEq]; have h:=model.positive; omega,?_⟩
  intro funded
  dsimp only
  intro continuing
  let output := evaluateHOLFiniteState (decClockHOLFinite source) body
  have summary := model.summary (decClockHOLFinite source)
  unfold LocalSummary at summary
  have normal : output.1=none := continuing.resolve_right summary.2.2.2
  have run : evaluateHOLFiniteState (decClockHOLFinite source) body=(none,output.2) := Prod.ext normal rfl
  have nextIndex : output.2.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+stride)))) := by
    simpa only [BitVec.ofNat_add] using model.advance (decClockHOLFinite source) output.2 (BitVec.ofNat 64 index) indexLocal run
  have nextLength := (summary.1 normal).trans lengthLocal
  have nextNumber : (BitVec.ofNat 64 (index+stride)).toNat=index+stride := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have h:=model.short; omega)]
  have nextRank : rank length output.2=length-(index+stride) := by simp [rank,CounterFlow.counterWord,nextIndex,valueWord,nextNumber]
  exact ⟨⟨index+stride,active,nextIndex,nextLength⟩,by rw [rankEq,nextRank]; have h:=model.positive; omega⟩

/-- All-outcome short-loop pricing at its real current bounded counter. -/
theorem Model.cost (code) (test : ExpHOL 64) (body : ProgHOL 64) (stride length : Nat) (model : Model code test body stride length)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) (installed : source.code=code) (inside : index≤length)
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source (.while test body)).2.clock≤length-index := by
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=code → valid length current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word word)) → word≠0 → current.clock≠0 →
      current.clock-1-(evaluateHOLFiniteState (decClockHOLFinite current) body).2.clock≤0 := by
    intro current codeEq ready word read nonzero funded
    have same := model.quiet (decClockHOLFinite current) codeEq
    change (evaluateHOLFiniteState (decClockHOLFinite current) body).2.clock=current.clock-1 at same
    omega
  have price := ClockCost.ranked_loop_current code test body 0 (valid length) (rank length) priced
    (by intro current codeEq ready word read nonzero; exact model.progress code test body stride length current ready word read nonzero)
    source installed ⟨index,inside,indexLocal,lengthLocal⟩
  have number : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have h:=model.short; omega)]
  simpa [rank,CounterFlow.counterWord,indexLocal,valueWord,number] using price

theorem Model.normal (code) (test : ExpHOL 64) (body : ProgHOL 64) (stride length : Nat) (model : Model code test body stride length)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : source.code=code) (ready : valid length source)
    (run : evaluateHOLFiniteState source (.while test body)=(none,post)) : valid length post := by
  apply loop_invariant_summary code (ofString "n") test body model.summary (valid length) _ source post installed ready run
  intro current codeEq currentValid word read nonzero funded target bodyRun
  have next := (model.progress code test body stride length current currentValid word read nonzero).2 funded
  rw [bodyRun] at next
  exact (next (Or.inl rfl)).1

theorem byte_model (code) (length : Nat) (short : length<32) : Model code (Zero.condition 8#64) Zero.byteBody 8 length := by
  refine ⟨by decide,short,?_,ZeroByteFlow.byte_advance,ZeroByteFlow.byte_summary (ofString "n") (by decide),ZeroByteFlow.byte_quiet code⟩
  intro source index inside indexLocal lengthLocal
  exact Zero.condition_read source index length 8 (by omega) inside (by decide) indexLocal lengthLocal

theorem tail_model (code) (length : Nat) (short : length<32) : Model code (.cmp .lower (localVar "i") (localVar "n")) Zero.tailBody 1 length := by
  refine ⟨by decide,short,?_,ZeroByteFlow.tail_advance,ZeroByteFlow.tail_summary (ofString "n") (by decide),ZeroByteFlow.tail_quiet code⟩
  intro source index inside indexLocal lengthLocal
  have read := Zero.tail_condition source index length (by omega) inside indexLocal lengthLocal
  have equivalent : (index<length)=(index+1≤length) := propext (by omega)
  simpa only [equivalent] using read

end InitECandidate.Solver.Input.ZeroShort

#print axioms InitECandidate.Solver.Input.ZeroShort.Model.cost
#print axioms InitECandidate.Solver.Input.ZeroShort.Model.normal
#print axioms InitECandidate.Solver.Input.ZeroShort.byte_model
#print axioms InitECandidate.Solver.Input.ZeroShort.tail_model
