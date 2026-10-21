import InitECandidate.Solver.Input.PayloadHashTransactionNormal
import InitECandidate.Solver.Input.ClockCostTerminatingSequence
import InitECandidate.Solver.Input.ClockCostTerminatingLoop
import InitECandidate.Solver.Input.CounterLoopCost
import InitECandidate.Solver.Input.VarList.RecordPointers

namespace InitECandidate.Solver.Input.PayloadHash.Transactions
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Packing/progressive hashing has a linear charge per actual transaction
byte, plus one fixed per-record overhead. No global slice maximum is used. -/
theorem byte_price (length : Nat) : length/8+115*PackBytes.chunks length+24283≤4*length+24398 := by
  unfold PackBytes.chunks
  omega

theorem step_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor stp accel chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (actual : RoundState source array roots cursor stp accel chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor stp accel chunk pointers lengths n capacity) (active : index<n)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source transactionStep=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤4*lengths index+24398 := by
  obtain ⟨outArena,temporary⟩ := call_geometry array roots cursor stp accel chunk pointers lengths n capacity index geometry active
  have args := arguments_read source array roots cursor stp accel chunk zeros pointers lengths n capacity index actual geometry active
  rw [loop_shapes.2.1] at run
  have price := ClockCost.sequence_terminating source post _ increment (lengths index/8+115*PackBytes.chunks (lengths index)+24283) 0
    (by intro observed target evaluated notTimeout
        exact PBytes.call_cost source target (pointers index) cursor (roots+BitVec.ofNat 64 (32*index)) stp accel chunk zeros (lengths index)
          (by have a:=geometry.lengthsBound index active; have b:=geometry.capacityBound; omega) actual.workspace actual.heap (geometry.inputs index active) temporary geometry.aligned outArena
          (some none) transactionArguments args observed evaluated notTimeout)
    (by intro middle normal observed target evaluated notTimeout
        have zero:=ClockCost.assign middle.code (ofString "i") (.op .add [localVar "i",.const 1#64]) middle rfl
        change middle.clock-(evaluateHOLFiniteState middle increment).2.clock≤0 at zero
        rw [evaluated] at zero
        exact zero)
    result run notTimeout
  have bound := byte_price (lengths index)
  omega

theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor stp accel chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n)
    (actual : RoundState source array roots cursor stp accel chunk zeros pointers lengths n index) :
    evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) transactionTest=some (.val (.word (if index<n then 1#64 else 0#64))) := by
  have iNumber : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have nNumber : (BitVec.ofNat 64 n).toNat=n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [evalHOLFinite,evalHOLExact,toExact,transactionTest,localVar,actual.position,actual.count,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,iNumber,nNumber,
    show index<9223372036854775808 from by omega,show n<9223372036854775808 from by omega]

theorem active_of_test (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor stp accel chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n)
    (actual : RoundState source array roots cursor stp accel chunk zeros pointers lengths n index)
    (word : BitVec 64) (read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) transactionTest=some (.val (.word word))) (nonzero : word≠0) : index<n := by
  have expected := test_read source array roots cursor stp accel chunk zeros pointers lengths n index bounded inside actual
  by_contra inactive
  rw [if_neg inactive] at expected
  have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero zero

def allowance (lengths : Nat→Nat) (n index : Nat) := 4*(VarList.sumPrefix lengths n-VarList.sumPrefix lengths index)+24399*(n-index)

theorem allowance_step (lengths : Nat→Nat) (n index : Nat) (active : index<n) :
    allowance lengths n index=4*lengths index+24399+allowance lengths n (index+1) := by
  have bound := VarList.sum_prefix_mono lengths (index+1) n (by omega)
  simp only [VarList.sumPrefix] at bound
  unfold allowance
  simp only [VarList.sumPrefix]
  omega

def valid (array roots cursor stp accel chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n : Nat)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  ∃ index : Nat,index≤n ∧ RoundState source array roots cursor stp accel chunk zeros pointers lengths n index

def remaining (lengths : Nat→Nat) (n : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  allowance lengths n (CounterFlow.counterWord source (ofString "i")).toNat

theorem remaining_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor stp accel chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n)
    (actual : RoundState source array roots cursor stp accel chunk zeros pointers lengths n index) : remaining lengths n source=allowance lengths n index := by
  have number : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp only [remaining,CounterFlow.counterWord,actual.position,Option.getD_some,valueWord,number]

/-- Actual original transaction loop is linear in the sum of the real
record lengths plus the real record count. All non-timeout failures remain. -/
theorem loop_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor stp accel chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (inside : index≤n) (actual : RoundState source array roots cursor stp accel chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor stp accel chunk pointers lengths n capacity)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source transactionLoop=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤allowance lengths n index := by
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → valid array roots cursor stp accel chunk zeros pointers lengths n current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) transactionTest=some (.val (.word word)) → word≠0 → current.clock≠0 →
      let output:=evaluateHOLFiniteState (decClockHOLFinite current) transactionStep
      output.1≠some .timeOut → current.clock-output.2.clock≤remaining lengths n current ∧
        ((output.1=none ∨ output.1=some .continue) → valid array roots cursor stp accel chunk zeros pointers lengths n output.2 ∧
          current.clock-output.2.clock+remaining lengths n output.2≤remaining lengths n current) := by
    intro current codeEq ready word read nonzero funded
    obtain ⟨position,positionBound,currentRound⟩ := ready
    have active := active_of_test current array roots cursor stp accel chunk zeros pointers lengths n position geometry.countBound positionBound currentRound word read nonzero
    have entryRound := RoundState.dec_clock current array roots cursor stp accel chunk zeros pointers lengths n position currentRound
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) transactionStep
    dsimp only
    intro bodyNotTimeout
    change current.clock-output.2.clock≤remaining lengths n current ∧
      ((output.1=none ∨ output.1=some .continue) → valid array roots cursor stp accel chunk zeros pointers lengths n output.2 ∧
        current.clock-output.2.clock+remaining lengths n output.2≤remaining lengths n current)
    have cost : current.clock-1-output.2.clock≤4*lengths position+24398 :=
      step_cost (decClockHOLFinite current) output.2 array roots cursor stp accel chunk zeros pointers lengths n capacity position entryRound geometry active output.1 rfl bodyNotTimeout
    have monotone : output.2.clock≤current.clock-1 := evaluateHOLFiniteState_clock_le (decClockHOLFinite current) transactionStep
    have currentAllowance := remaining_read current array roots cursor stp accel chunk zeros pointers lengths n position geometry.countBound positionBound currentRound
    have budget := allowance_step lengths n position active
    refine ⟨by rw [currentAllowance]; omega,?_⟩
    intro continuing
    have summary := (transaction_step_local (ofString "txs") (by decide)).summary_full (decClockHOLFinite current)
    unfold LocalSummary at summary
    have normal : output.1=none := continuing.resolve_right summary.2.2.2
    have bodyRun : evaluateHOLFiniteState (decClockHOLFinite current) transactionStep=(none,output.2) := Prod.ext normal rfl
    have next := step_normal (decClockHOLFinite current) output.2 array roots cursor stp accel chunk zeros pointers lengths n capacity position entryRound geometry active bodyRun
    have nextAllowance := remaining_read output.2 array roots cursor stp accel chunk zeros pointers lengths n (position+1) geometry.countBound (by omega) next
    refine ⟨⟨position+1,by omega,next⟩,?_⟩
    rw [currentAllowance,nextAllowance]
    omega
  have observed : (evaluateHOLFiniteState source (.while transactionTest transactionStep)).1≠some .timeOut := by rw [←loop_shapes.1,run]; exact notTimeout
  have price := ClockCost.potential_loop_terminating source.code transactionTest transactionStep (valid array roots cursor stp accel chunk zeros pointers lengths n) (remaining lengths n) priced source rfl ⟨index,inside,actual⟩ observed
  rw [←loop_shapes.1,run] at price
  change source.clock-post.clock≤remaining lengths n source at price
  rw [remaining_read source array roots cursor stp accel chunk zeros pointers lengths n index geometry.countBound inside actual] at price
  exact price

end InitECandidate.Solver.Input.PayloadHash.Transactions

#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.byte_price
#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.step_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.test_read
#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.active_of_test
#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.allowance_step
#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.remaining_read
#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.loop_cost
