import InitECandidate.Solver.CurrentKeccak.HashSyntax
import InitECandidate.Solver.CurrentKeccak.AbsorbCost
import InitECandidate.Solver.CurrentKeccak.AbsorbCall
import InitECandidate.Solver.Input.ClockCostCurrentLoop
import InitECandidate.Solver.Input.CounterStrideCost
import InitECandidate.Solver.Input.LoopNormalExit

namespace InitECandidate.Solver.CurrentKeccak.Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input Input.CounterFlow

theorem block_safe : LocalPrefix (ofString "n") blockBody :=
  .seq (.call none _ _ (by intro name impossible; cases impossible)) (.assign _ _ (by decide))

theorem block_advance : Advances (ofString "i") 136 blockBody := by
  change Advances (ofString "i") (0+136) (.seq _ _)
  apply CounterFlow.sequence
  · exact CounterFlow.preserved _ _ (.call none _ _ (by intro name impossible; cases impossible))
  · exact CounterFlow.increment_by _ 136

theorem block_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code blockBody 43 := by
  simpa only [blockBody,Nat.add_zero] using ClockCost.sequence code _ _ 43 0
    (Absorb.call_cost code installed blockArguments) (ClockCost.assign code _ _)

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
    source.clock-(evaluateHOLFiniteState source blocks).2.clock≤44*(length/136) := by
  have priced:=CounterFlow.stride_loop_cost source.code condition blockBody 136 length 43 (by decide) (by omega)
    block_advance block_safe.summary_full (test_reads length small) (block_cost source.code installed) source rfl valid
  exact Nat.le_trans priced (Nat.mul_le_mul_left 44 (Nat.div_le_div_right (Nat.sub_le _ _)))

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

/-- A real block loop's current pointer and counter. After its first
successful read the pointer and their ordinary sum are below fixed memory
limits, so neither pointer addition nor counter advance can wrap. -/
structure DomainBlockState (pointer count stp : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : BitVec 64) : Prop where
  domain : source.memaddrs=InitE.ordinaryDomain
  pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer))
  countCell : source.locals.lookup (ofString "n")=some (.val (.word count))
  stateCell : source.locals.lookup (ofString "stp")=some (.val (.word stp))
  counter : source.locals.lookup (ofString "i")=some (.val (.word index))
  bounded : index.toNat≤CopyAny.ordinaryEnd+136
  belowCount : index.toNat≤count.toNat
  started : index≠0#64 → pointer.toNat<CopyAny.ordinaryEnd ∧
    pointer.toNat+index.toNat≤CopyAny.ordinaryEnd+136

private theorem DomainBlockState.decClock
    {pointer count stp index : BitVec 64} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    (ready : DomainBlockState pointer count stp source index) :
    DomainBlockState pointer count stp (decClockHOLFinite source) index :=
  ⟨ready.domain,ready.pointerCell,ready.countCell,ready.stateCell,ready.counter,
    ready.bounded,ready.belowCount,ready.started⟩

private theorem domain_test (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (index count : BitVec 64)
    (counter : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (bounded : index.toNat≤CopyAny.ordinaryEnd+136) :
    evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) condition=
      some (.val (.word (if index.toNat+136≤count.toNat then 1#64 else 0#64))) := by
  have sum : (index+136#64).toNat=index.toNat+136 := by
    rw [BitVec.toNat_add_of_lt (by unfold CopyAny.ordinaryEnd at bounded; change index.toNat+136<2^64; omega)]
    rfl
  by_cases active : index.toNat+136≤count.toNat
  · have lower : ¬count<index+136#64 := by
      change ¬count.toNat<(index+136#64).toNat
      rw [sum]
      omega
    simp [evalHOLFinite,evalHOLExact,evalListHOLExact,toExact,condition,localVar,addConst,
      counter,countCell,valueIsWord,valueWord,wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,lower,active]
  · have lower : count<index+136#64 := by
      change count.toNat<(index+136#64).toNat
      rw [sum]
      omega
    simp [evalHOLFinite,evalHOLExact,evalListHOLExact,toExact,condition,localVar,addConst,
      counter,countCell,valueIsWord,valueWord,wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,lower,active]

private theorem domain_active (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer count stp index observed : BitVec 64) (ready : DomainBlockState pointer count stp source index)
    (read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) condition=some (.val (.word observed)))
    (nonzero : observed≠0#64) : index.toNat+136≤count.toNat := by
  have expected:=domain_test source index count ready.counter ready.countCell ready.bounded
  by_contra inactive
  rw [if_neg inactive] at expected
  have zero : observed=0#64 := by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero zero

def domainBlockRank (index : BitVec 64) : Nat := (CopyAny.ordinaryEnd+136-index.toNat)/136+1

/-- Every actual continuing block derives the next bounded state from its
mandatory input read. Failed blocks need no successor or future read. -/
theorem domain_block_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer count stp index : BitVec 64) (installed : OriginalCode.Installed source.code)
    (ready : DomainBlockState pointer count stp source index)
    (active : index.toNat+136≤count.toNat)
    (run : evaluateHOLFiniteState source blockBody=(none,post)) :
    DomainBlockState pointer count stp post (index+136#64) ∧
      domainBlockRank (index+136#64)<domainBlockRank index := by
  obtain ⟨middle,front,back⟩:=Input.sequence_none source post _ _ run
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) blockArguments=
      some (Absorb.values stp (pointer+index)) := by
    simp [blockArguments,Absorb.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,
      ready.pointerCell,ready.stateCell,ready.counter,valueIsWord,valueWord,wordOpHOL,wordOp]
  have mappedUpper:=Absorb.call_input_upper source middle stp (pointer+index) installed ready.domain blockArguments args front
  have sumUpper : pointer.toNat+index.toNat<CopyAny.ordinaryEnd := by
    by_cases zero : index=0#64
    · subst index
      simpa only [BitVec.add_zero,BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero] using mappedUpper
    · obtain ⟨pointerBound,sumBound⟩:=ready.started zero
      rw [BitVec.toNat_add_of_lt (by unfold CopyAny.ordinaryEnd at sumBound; omega)] at mappedUpper
      exact mappedUpper
  have nextNumber : (index+136#64).toNat=index.toNat+136 := by
    rw [BitVec.toNat_add_of_lt (by unfold CopyAny.ordinaryEnd at sumUpper; change index.toNat+136<2^64; omega)]
    rfl
  have keep (key : MlS) (different : key≠ofString "i") : post.locals.lookup key=source.locals.lookup key := by
    have safe : LocalPrefix key blockBody :=
      .seq (.call none _ _ (by intro name impossible; cases impossible)) (.assign _ _ different)
    have summary:=safe.summary_full source
    unfold LocalSummary at summary
    rw [run] at summary
    exact summary.1 rfl
  have nextCounter:=block_advance source post index ready.counter run
  have nextDomain:=(evaluation_fields source post blockBody none run).1.trans ready.domain
  refine ⟨⟨nextDomain,(keep _ (by decide)).trans ready.pointerCell,(keep _ (by decide)).trans ready.countCell,
    (keep _ (by decide)).trans ready.stateCell,nextCounter,?_,?_,?_⟩,?_⟩
  · rw [nextNumber]
    omega
  · rw [nextNumber]
    exact active
  · intro nonzero
    rw [nextNumber]
    omega
  · have difference : CopyAny.ordinaryEnd+136-index.toNat=
        (CopyAny.ordinaryEnd+136-(index.toNat+136))+136 := by omega
    simp only [domainBlockRank,nextNumber]
    rw [difference,Nat.add_div_right _ (by decide : 0<136)]
    omega

/-- Every block-loop outcome has a fixed spatial price even if its initial
64-bit count is near word wraparound. The last failed read is included. -/
theorem blocks_domain_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer count stp index : BitVec 64) (installed : OriginalCode.Installed source.code)
    (ready : DomainBlockState pointer count stp source index) :
    source.clock-(evaluateHOLFiniteState source blocks).2.clock≤44*domainBlockRank index := by
  exact ClockCost.ranked_loop_indexed source.code condition blockBody 43
    (DomainBlockState pointer count stp) domainBlockRank
    (by intro state current codeEq valid observed read nonzero funded
        have bound:=block_cost source.code installed (decClockHOLFinite state) codeEq
        exact bound)
    (by intro state current codeEq valid observed read nonzero
        refine ⟨by exact Nat.zero_lt_succ _,?_⟩
        intro funded
        dsimp only
        intro continuing
        let output:=evaluateHOLFiniteState (decClockHOLFinite state) blockBody
        have safe:=block_safe.summary_full (decClockHOLFinite state)
        unfold LocalSummary at safe
        have normal : output.1=none := continuing.resolve_right safe.2.2.2
        have run : evaluateHOLFiniteState (decClockHOLFinite state) blockBody=(none,output.2) := Prod.ext normal rfl
        have actualInstalled : OriginalCode.Installed (decClockHOLFinite state).code := by
          change OriginalCode.Installed state.code
          rw [codeEq]
          exact installed
        have next:=domain_block_normal (decClockHOLFinite state) output.2 pointer count stp current actualInstalled valid.decClock
          (domain_active state pointer count stp current observed valid read nonzero) run
        exact ⟨current+136#64,next⟩)
    source index rfl ready

/-- A genuine normal loop exit derives a small count and remainder. The
small-count premise used by padding follows from the actual memory reads. -/
theorem blocks_domain_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer count stp index : BitVec 64) (installed : OriginalCode.Installed source.code)
    (ready : DomainBlockState pointer count stp source index)
    (normal : evaluateHOLFiniteState source blocks=(none,post)) :
    ∃ word,DomainBlockState pointer count stp post word ∧ count.toNat-word.toNat<136 ∧
      count.toNat<CopyAny.ordinaryEnd+272 := by
  have valid : ∃ word,DomainBlockState pointer count stp post word := by
    apply Input.loop_invariant source.code (ofString "n") condition blockBody block_safe
      (fun current=>∃ word,DomainBlockState pointer count stp current word) ?_ source post rfl ⟨index,ready⟩ normal
    intro current codeEq currentReady observed read nonzero funded target run
    obtain ⟨word,valid⟩:=currentReady
    have currentInstalled : OriginalCode.Installed (decClockHOLFinite current).code := by
      change OriginalCode.Installed current.code
      rw [codeEq]
      exact installed
    exact ⟨word+136#64,(domain_block_normal (decClockHOLFinite current) target pointer count stp word currentInstalled valid.decClock
      (domain_active current pointer count stp word observed valid read nonzero) run).1⟩
  obtain ⟨word,valid⟩:=valid
  have ended:=Input.loop_normal_exit condition blockBody (fun current=>(block_safe.summary_full current).2.2.1) source post normal
  have test:=domain_test post word count valid.counter valid.countCell valid.bounded
  have inactive : ¬word.toNat+136≤count.toNat := by
    intro active
    rw [if_pos active] at test
    have contradiction:=ended.symm.trans test
    cases contradiction
  refine ⟨word,valid,by omega,?_⟩
  have bounded:=valid.bounded
  omega

end InitECandidate.Solver.CurrentKeccak.Hash

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.block_advance
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.test_reads
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.blocks_cost
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.blocks_normal

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.domain_block_normal
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.blocks_domain_cost
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.blocks_domain_normal
