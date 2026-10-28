import InitECandidate.Solver.Input.CurrentHash.PayloadTransactionStep
import InitECandidate.Solver.Input.ClockCostTerminatingSequence
import InitECandidate.Solver.Input.ClockCostTerminatingLoop
import InitECandidate.Solver.Input.CounterLoopCost
import InitECandidate.Solver.Input.VarList.PrefixSum
import InitECandidate.Solver.Input.LoopInvariant

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Current byte-hash allowance is linear in that actual item's length. -/
theorem byte_price (length : Nat) : PackBytesCost.price length+88*PackBytes.chunks length+3173≤5*length+3302 := by
  have pack:=PackBytesCost.price_bound length
  unfold CopyAny.price PackBytes.chunks at *
  omega

theorem step_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (actual : RoundState source array roots cursor chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor chunk pointers lengths n capacity) (active : index<n)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source transactionStep=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤5*lengths index+3302 := by
  have args := arguments_read source array roots cursor chunk zeros pointers lengths n capacity index actual geometry active
  have lengthBound := geometry.lengthsBound index active
  have capacityBound := geometry.capacityBound
  have chunksBound : PackBytes.chunks (lengths index)≤134217728 := by unfold PackBytes.chunks; omega
  rw [loop_shapes.2.1] at run
  have price := ClockCost.sequence_terminating source post _ increment (PackBytesCost.price (lengths index)+88*PackBytes.chunks (lengths index)+3173) 0
    (by intro observed target evaluated noTimeout
        exact PBytesCost.call_cost source target (pointers index) (roots+BitVec.ofNat 64 (32*index)) (lengths index)
          actual.context.installed (by omega) chunksBound (some none) transactionArguments args observed evaluated noTimeout)
    (by intro middle normal observed target evaluated noTimeout
        have zero:=ClockCost.assign middle.code (ofString "i") (.op .add [localVar "i",.const 1#64]) middle rfl
        change middle.clock-(evaluateHOLFiniteState middle increment).2.clock≤0 at zero
        rw [evaluated] at zero
        exact zero)
    result run notTimeout
  have bound := byte_price (lengths index)
  omega

theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n)
    (actual : RoundState source array roots cursor chunk zeros pointers lengths n index) :
    evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) transactionTest=some (.val (.word (if index<n then 1#64 else 0#64))) := by
  have iNumber : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have nNumber : (BitVec.ofNat 64 n).toNat=n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [evalHOLFinite,evalHOLExact,toExact,transactionTest,localVar,actual.position,actual.count,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,iNumber,nNumber,
    show index<9223372036854775808 from by omega,show n<9223372036854775808 from by omega]

theorem active_of_test (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n)
    (actual : RoundState source array roots cursor chunk zeros pointers lengths n index)
    (word : BitVec 64) (read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) transactionTest=some (.val (.word word))) (nonzero : word≠0) : index<n := by
  have expected := test_read source array roots cursor chunk zeros pointers lengths n index bounded inside actual
  by_cases active : index<n
  · exact active
  have inactive : ¬index<n := active
  rw [if_neg inactive] at expected
  have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact False.elim (nonzero zero)

def allowance (lengths : Nat→Nat) (n index : Nat) := 5*(VarList.sumPrefix lengths n-VarList.sumPrefix lengths index)+3303*(n-index)

theorem allowance_step (lengths : Nat→Nat) (n index : Nat) (active : index<n) :
    allowance lengths n index=5*lengths index+3303+allowance lengths n (index+1) := by
  have bound := VarList.sum_prefix_mono lengths (index+1) n (by omega)
  simp only [VarList.sumPrefix] at bound
  unfold allowance
  simp only [VarList.sumPrefix]
  omega

def valid (array roots cursor chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n : Nat)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  ∃ index : Nat,index≤n ∧ RoundState source array roots cursor chunk zeros pointers lengths n index

def remaining (lengths : Nat→Nat) (n : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  allowance lengths n (CounterFlow.counterWord source (ofString "i")).toNat

theorem remaining_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n)
    (actual : RoundState source array roots cursor chunk zeros pointers lengths n index) : remaining lengths n source=allowance lengths n index := by
  have number : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp only [remaining,CounterFlow.counterWord,actual.position,Option.getD_some,valueWord,number]

/-- Actual original transaction loop is linear in the sum of the real
record lengths plus the real record count. All non-timeout failures remain. -/
theorem loop_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (inside : index≤n) (actual : RoundState source array roots cursor chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor chunk pointers lengths n capacity)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source transactionLoop=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤allowance lengths n index := by
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → valid array roots cursor chunk zeros pointers lengths n current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) transactionTest=some (.val (.word word)) → word≠0 → current.clock≠0 →
      let output:=evaluateHOLFiniteState (decClockHOLFinite current) transactionStep
      output.1≠some .timeOut → current.clock-output.2.clock≤remaining lengths n current ∧
        ((output.1=none ∨ output.1=some .continue) → valid array roots cursor chunk zeros pointers lengths n output.2 ∧
          current.clock-output.2.clock+remaining lengths n output.2≤remaining lengths n current) := by
    intro current codeEq ready word read nonzero funded
    obtain ⟨position,positionBound,currentRound⟩ := ready
    have active := active_of_test current array roots cursor chunk zeros pointers lengths n position geometry.countBound positionBound currentRound word read nonzero
    have entryRound := currentRound.dec_clock
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) transactionStep
    dsimp only
    intro bodyNotTimeout
    change current.clock-output.2.clock≤remaining lengths n current ∧
      ((output.1=none ∨ output.1=some .continue) → valid array roots cursor chunk zeros pointers lengths n output.2 ∧
        current.clock-output.2.clock+remaining lengths n output.2≤remaining lengths n current)
    have cost : current.clock-1-output.2.clock≤5*lengths position+3302 :=
      step_cost (decClockHOLFinite current) output.2 array roots cursor chunk zeros pointers lengths n capacity position entryRound geometry active output.1 rfl bodyNotTimeout
    have monotone : output.2.clock≤current.clock-1 := evaluateHOLFiniteState_clock_le (decClockHOLFinite current) transactionStep
    have currentAllowance := remaining_read current array roots cursor chunk zeros pointers lengths n position geometry.countBound positionBound currentRound
    have budget := allowance_step lengths n position active
    refine ⟨by rw [currentAllowance]; omega,?_⟩
    intro continuing
    have summary := (transaction_step_local (ofString "txs") (by decide)).summary_full (decClockHOLFinite current)
    unfold LocalSummary at summary
    have normal : output.1=none := continuing.resolve_right summary.2.2.2
    have bodyRun : evaluateHOLFiniteState (decClockHOLFinite current) transactionStep=(none,output.2) := Prod.ext normal rfl
    have next := step_normal (decClockHOLFinite current) output.2 array roots cursor chunk zeros pointers lengths n capacity position entryRound geometry active bodyRun
    have nextAllowance := remaining_read output.2 array roots cursor chunk zeros pointers lengths n (position+1) geometry.countBound (by omega) next
    refine ⟨⟨position+1,by omega,next⟩,?_⟩
    rw [currentAllowance,nextAllowance]
    omega
  have observed : (evaluateHOLFiniteState source (.while transactionTest transactionStep)).1≠some .timeOut := by rw [←loop_shapes.1,run]; exact notTimeout
  have price := ClockCost.potential_loop_terminating source.code transactionTest transactionStep (valid array roots cursor chunk zeros pointers lengths n) (remaining lengths n) priced source rfl ⟨index,inside,actual⟩ observed
  rw [←loop_shapes.1,run] at price
  change source.clock-post.clock≤remaining lengths n source at price
  rw [remaining_read source array roots cursor chunk zeros pointers lengths n index geometry.countBound inside actual] at price
  exact price

/-- Same real normal loop retains its current bounded index and complete
physical transaction image, without a supplied future iteration trace. -/
theorem loop_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (inside : index≤n) (data : RoundState source array roots cursor chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor chunk pointers lengths n capacity)
    (actual : evaluateHOLFiniteState source transactionLoop=(none,post)) : valid array roots cursor chunk zeros pointers lengths n post := by
  have transition : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → valid array roots cursor chunk zeros pointers lengths n current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) transactionTest=some (.val (.word word)) → word≠0 → current.clock≠0 → ∀ target,
      evaluateHOLFiniteState (decClockHOLFinite current) transactionStep=(none,target) → valid array roots cursor chunk zeros pointers lengths n target := by
    intro current codeEq currentValid word read nonzero funded target bodyRun
    obtain ⟨position,positionBound,ready⟩ := currentValid
    have active := active_of_test current array roots cursor chunk zeros pointers lengths n position geometry.countBound positionBound ready word read nonzero
    have next := step_normal (decClockHOLFinite current) target array roots cursor chunk zeros pointers lengths n capacity position ready.dec_clock geometry active bodyRun
    exact ⟨position+1,by omega,next⟩
  rw [loop_shapes.1] at actual
  exact loop_invariant source.code (ofString "txs") transactionTest transactionStep (transaction_step_local (ofString "txs") (by decide))
    (valid array roots cursor chunk zeros pointers lengths n) transition source post rfl ⟨index,inside,data⟩ actual

end InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.byte_price
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.step_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.test_read
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.active_of_test
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.allowance_step
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.remaining_read
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.loop_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.loop_normal
