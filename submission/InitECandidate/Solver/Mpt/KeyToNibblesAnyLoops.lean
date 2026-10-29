import InitECandidate.Solver.Mpt.KeyToNibblesAnyFlow
import InitECandidate.Solver.Input.CounterStrideCost
import InitECandidate.Solver.Input.WhileNormalGuard
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem block_reads (length : Nat) (small : length+4<2^64) : Input.CounterFlow.StrideReads blockCondition 4 length := by
  intro source word iCell nCell inside
  have lengthNumber : (BitVec.ofNat 64 length).toNat=length:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have number : (word+4#64).toNat=word.toNat+4:=by rw [BitVec.toNat_add_of_lt (by change word.toNat+4<2^64; omega)]; rfl
  by_cases active : word.toNat+4≤length
  · have comparison : ¬BitVec.ofNat 64 length<word+4#64:=by change ¬(BitVec.ofNat 64 length).toNat<(word+4#64).toNat; rw [lengthNumber,number]; omega
    simp [blockCondition,evalHOLFinite,evalHOLExact,evalListHOLExact,addConst,localVar,toExact,iCell,nCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,comparison,active]
  · have comparison : BitVec.ofNat 64 length<word+4#64:=by change (BitVec.ofNat 64 length).toNat<(word+4#64).toNat; rw [lengthNumber,number]; omega
    simp [blockCondition,evalHOLFinite,evalHOLExact,evalListHOLExact,addConst,localVar,toExact,iCell,nCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,comparison,active]

theorem tail_reads (length : Nat) (small : length<2^64) : Input.CounterFlow.StrideReads tailCondition 1 length := by
  intro source word iCell nCell inside
  have lengthNumber : (BitVec.ofNat 64 length).toNat=length:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  by_cases active : word.toNat+1≤length
  · have comparison : word<BitVec.ofNat 64 length:=by change word.toNat<(BitVec.ofNat 64 length).toNat; rw [lengthNumber]; omega
    simp [tailCondition,evalHOLFinite,evalHOLExact,localVar,toExact,iCell,nCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,comparison,active]
  · have comparison : ¬word<BitVec.ofNat 64 length:=by change ¬word.toNat<(BitVec.ofNat 64 length).toNat; rw [lengthNumber]; omega
    simp [tailCondition,evalHOLFinite,evalHOLExact,localVar,toExact,iCell,nCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,comparison,active]

/-- A real normal four-byte loop leaves at most three bytes for the tail.
Its actual counter and false final guard follow from execution. -/
theorem block_normal_remainder (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+4<2^64) (valid : Input.CounterFlow.StrideInvariant length source)
    (normal : evaluateHOLFiniteState source blockLoop=(none,target)) :
    ∃ word,target.locals.lookup (ofString "i")=some (.val (.word word)) ∧
      target.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))) ∧ word.toNat≤length ∧ length-word.toNat≤3 := by
  rw [loop_shapes.1] at normal
  have next:=Input.CounterFlow.stride_loop_normal source.code blockCondition blockBody 4 length (by decide) (by omega)
    bodies_advance.1 bodies_length_summary.1 (block_reads length small) source target rfl valid normal
  obtain ⟨word,iCell,nCell,inside⟩:=next
  have stopped:=Input.while_normal_guard blockCondition blockBody (fun current=>(bodies_length_summary.1 current).2.2) source target normal
  have actual:=block_reads length small target word iCell nCell inside
  have remainder : length-word.toNat≤3:=by
    by_cases short : length-word.toNat≤3
    · exact short
    · exfalso
      have active : word.toNat+4≤length:=by omega
      rw [if_pos active] at actual
      have impossible : (0#64 : BitVec 64)=1#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using stopped.symm.trans actual
      exact (by decide : (0#64 : BitVec 64)≠1#64) impossible
  exact ⟨word,iCell,nCell,inside,remainder⟩

/-- Both actual loops cost at most one tick per four-byte block plus three
tail ticks, without source/destination mapping or successful-store premises. -/
theorem loops_any_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) (word : BitVec 64)
    (small : length+4<2^64)
    (iCell : source.locals.lookup (ofString "i")=some (.val (.word word)))
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))) (inside : word.toNat≤length) :
    source.clock-(evaluateHOLFiniteState source (.seq blockLoop (.seq tailLoop afterTail))).2.clock≤(length-word.toNat)/4+3 := by
  have valid : Input.CounterFlow.StrideInvariant length source:=⟨word,iCell,nCell,inside⟩
  have blockPrice:=Input.CounterFlow.stride_loop_cost source.code blockCondition blockBody 4 length 0 (by decide) (by omega)
    bodies_advance.1 bodies_length_summary.1 (block_reads length small) (Input.ClockCost.of_quiet source.code _ (bodies_quiet source.code).1) source rfl valid
  have actualBlockPrice : source.clock-(evaluateHOLFiniteState source blockLoop).2.clock≤(length-word.toNat)/4:=by
    rw [loop_shapes.1]
    simpa only [Nat.zero_add,Nat.one_mul,Input.CounterFlow.strideRank,Input.CounterFlow.counterWord,iCell,Option.getD_some,valueWord] using blockPrice
  apply Input.ClockCost.sequence_reached_current source blockLoop (.seq tailLoop afterTail) ((length-word.toNat)/4) 3 actualBlockPrice
  intro middle normal
  obtain ⟨next,iNext,nNext,nextInside,remainder⟩:=block_normal_remainder source middle length small valid normal
  have nextValid : Input.CounterFlow.StrideInvariant length middle:=⟨next,iNext,nNext,nextInside⟩
  have tailPrice:=Input.CounterFlow.stride_loop_cost middle.code tailCondition tailBody 1 length 0 (by decide) (by omega)
    bodies_advance.2 bodies_length_summary.2 (tail_reads length (by omega)) (Input.ClockCost.of_quiet middle.code _ (bodies_quiet middle.code).2) middle rfl nextValid
  have actualTailPrice : middle.clock-(evaluateHOLFiniteState middle tailLoop).2.clock≤3:=by
    rw [loop_shapes.2]
    simp only [Nat.zero_add,Nat.one_mul,Input.CounterFlow.strideRank,Input.CounterFlow.counterWord,iNext,Option.getD_some,valueWord,Nat.div_one] at tailPrice
    exact Nat.le_trans tailPrice remainder
  have footer : Input.ClockCost.Bound middle.code afterTail 0:=by rw [after_tail_shape]; exact Input.ClockCost.returned middle.code _
  exact Input.ClockCost.sequence_current middle tailLoop afterTail 3 0 actualTailPrice footer

theorem body_any_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) (small : length+4<2^64)
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤length/4+3 := by
  rw [body_shape]
  apply Input.ClockCost.declared_current source "i" (.const 0#64) 0#64 _ (length/4+3) rfl
  have currentN : (QueryBranch.bind source "i" 0#64).locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=
    (bind_lookup_other source "i" "n" 0#64 (by decide)).trans nCell
  exact loops_any_cost (QueryBranch.bind source "i" 0#64) length 0#64 small (bind_lookup_same _ _ _) currentN (by change 0≤length; omega)

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.block_reads
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.tail_reads
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.block_normal_remainder
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.loops_any_cost
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.body_any_cost
