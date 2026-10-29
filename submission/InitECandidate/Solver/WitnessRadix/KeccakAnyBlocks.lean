import InitECandidate.Solver.WitnessRadix.KeccakAbsorbAnyCost
import InitECandidate.Solver.Input.CounterStrideCost
import InitECandidate.Solver.Input.LoopNormalExit

namespace InitECandidate.Solver.WitnessRadix.Keccak256.AnyCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch Input Input.CounterFlow

theorem block_safe : LocalPrefix (ofString "n") blockBody :=
  .seq (.call none _ _ (by intro name impossible; cases impossible)) (.assign _ _ (by decide))

theorem block_advance : Advances (ofString "i") 136 blockBody := by
  change Advances (ofString "i") (0+136) (.seq _ _)
  apply CounterFlow.sequence
  · exact CounterFlow.preserved _ _ (.call none _ _ (by intro name impossible; cases impossible))
  · exact CounterFlow.increment_by _ 136

theorem block_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code blockBody 19 := by
  simpa only [blockBody,CopyBytes.increment,Nat.add_zero] using ClockCost.sequence code _ _ 19 0
    (KeccakAbsorb.call_cost code installed blockArguments) (ClockCost.assign code _ _)

theorem test_reads (length : Nat) (small : length+136<2^64) : StrideReads condition 136 length := by
  intro source word counter count bounded
  have encoded : (BitVec.ofNat 64 length).toNat=length:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have sum : (word+136#64).toNat=word.toNat+136:=by
    rw [BitVec.toNat_add_of_lt (by change word.toNat+136<2^64; omega)]; rfl
  by_cases active : word.toNat+136≤length
  · have lower : ¬BitVec.ofNat 64 length<word+136#64:=by change ¬(BitVec.ofNat 64 length).toNat<(word+136#64).toNat; rw [encoded,sum]; omega
    simp [evalHOLFinite,evalHOLExact,evalListHOLExact,toExact,condition,localVar,addConst,counter,count,valueIsWord,valueWord,wordOpHOL,wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,lower,active]
  · have lower : BitVec.ofNat 64 length<word+136#64:=by change (BitVec.ofNat 64 length).toNat<(word+136#64).toNat; rw [encoded,sum]; omega
    simp [evalHOLFinite,evalHOLExact,evalListHOLExact,toExact,condition,localVar,addConst,counter,count,valueIsWord,valueWord,wordOpHOL,wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,lower,active]

theorem blocks_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+136<2^64) (installed : OriginalCode.Installed source.code) (valid : StrideInvariant length source) :
    source.clock-(evaluateHOLFiniteState source blocks).2.clock≤20*(length/136) := by
  have priced:=CounterFlow.stride_loop_cost source.code condition blockBody 136 length 19 (by decide) (by omega)
    block_advance block_safe.summary_full (test_reads length small) (block_cost source.code installed) source rfl valid
  exact priced.trans (Nat.mul_le_mul_left 20 (Nat.div_le_div_right (Nat.sub_le _ _)))

/-- A genuine normal hash-block loop leaves its actual remainder below a
single block. This is derived from the final test, not assumed at padding. -/
theorem blocks_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+136<2^64) (valid : StrideInvariant length source)
    (normal : evaluateHOLFiniteState source blocks=(none,post)) :
    ∃ word,post.locals.lookup (ofString "i")=some (.val (.word word)) ∧
      post.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))) ∧ word.toNat≤length ∧ length-word.toNat<136 := by
  have next:=CounterFlow.stride_loop_normal source.code condition blockBody 136 length (by decide) (by omega)
    block_advance block_safe.summary_full (test_reads length small) source post rfl valid normal
  obtain ⟨word,counter,count,bounded⟩:=next
  have ended:=Input.loop_normal_exit condition blockBody (fun current=>(block_safe.summary_full current).2.2.1) source post normal
  have read:=test_reads length small post word counter count bounded
  have inactive : ¬word.toNat+136≤length:=by
    intro active
    rw [if_pos active] at read
    have contradiction:=ended.symm.trans read
    cases contradiction
  exact ⟨word,counter,count,bounded,by omega⟩

end InitECandidate.Solver.WitnessRadix.Keccak256.AnyCost

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.AnyCost.block_advance
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.AnyCost.test_reads
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.AnyCost.blocks_cost
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.AnyCost.blocks_normal
