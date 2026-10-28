import InitECandidate.Solver.Input.CurrentHash.PayloadProgram
import InitECandidate.Solver.Input.CurrentHash.FixedRecordCost
import InitECandidate.Solver.Input.CounterLoopCost
import InitECandidate.Solver.Input.ClockCostTerminatingLoop
import InitECandidate.Solver.Input.ClockCostTerminatingSequence
import InitECandidate.Solver.Input.IgnoredCallLookup
import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.Input.LoopInvariant

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash.Withdrawals
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure RoundState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n index : Nat) : Prop where
  installed : OriginalCode.Installed source.code
  pointer : source.locals.lookup (ofString "wd")=some (.val (.word p))
  root : source.locals.lookup (ofString "roots")=some (.val (.word roots))
  count : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 n)))
  position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))

theorem RoundState.dec_clock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {p roots : BitVec 64} {n index : Nat}
    (data : RoundState source p roots n index) : RoundState (decClockHOLFinite source) p roots n index :=
  ⟨data.installed,data.pointer,data.root,data.count,data.position⟩

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n index : Nat)
    (data : RoundState source p roots n index) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) withdrawalArguments=
      some (FixedRecord.scalarValues (p+BitVec.ofNat 64 (44*index)) (roots+BitVec.ofNat 64 (32*index))) := by
  simp [withdrawalArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.pointer,data.position,data.root,
    FixedRecord.scalarValues,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]

theorem step_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n index : Nat)
    (data : RoundState source p roots n index) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source withdrawalStep=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤759 := by
  rw [loop_shapes.2.2.2] at actual
  have cost := ClockCost.sequence_terminating source post _ increment 759 0
    (by intro observed target evaluated noTimeout
        exact FixedRecord.call_cost .withdrawal source target (p+BitVec.ofNat 64 (44*index)) (roots+BitVec.ofNat 64 (32*index))
          data.installed (some none) withdrawalArguments (arguments_read source p roots n index data) observed evaluated noTimeout)
    (by intro middle normal observed target evaluated noTimeout
        have zero:=ClockCost.assign middle.code (ofString "i") (.op .add [localVar "i",.const 1#64]) middle rfl
        change middle.clock-(evaluateHOLFiniteState middle increment).2.clock≤0 at zero
        rw [evaluated] at zero
        exact zero) result actual notTimeout
  omega

theorem step_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n index : Nat)
    (data : RoundState source p roots n index) (actual : evaluateHOLFiniteState source withdrawalStep=(none,post)) : RoundState post p roots n (index+1) := by
  rw [loop_shapes.2.2.2] at actual
  obtain ⟨middle,normal,advanced⟩ := Input.sequence_none source post _ increment actual
  have kept (name : String) := CallNormal.ignored_lookup source middle (ofString name) (ofString "htr_withdrawal") withdrawalArguments normal
  have position := (kept "i").trans data.position
  have read : eval middle (.op .add [localVar "i",.const 1#64])=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,position,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  have endpoint := assign_none middle post "i" _ (BitVec.ofNat 64 (index+1)) read advanced
  have installed : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle _ none normal).2.2.2]; exact data.installed
  rw [endpoint]
  exact ⟨installed,(bind_lookup_other middle "i" "wd" _ (by decide)).trans (kept "wd") |>.trans data.pointer,
    (bind_lookup_other middle "i" "roots" _ (by decide)).trans (kept "roots") |>.trans data.root,
    (bind_lookup_other middle "i" "nwd" _ (by decide)).trans (kept "nwd") |>.trans data.count,bind_lookup_same _ _ _⟩

theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n) (actual : RoundState source p roots n index) :
    evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) withdrawalTest=some (.val (.word (if index<n then 1#64 else 0#64))) := by
  have iNumber : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have nNumber : (BitVec.ofNat 64 n).toNat=n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [evalHOLFinite,evalHOLExact,toExact,withdrawalTest,localVar,actual.position,actual.count,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,iNumber,nNumber,
    show index<9223372036854775808 from by omega,show n<9223372036854775808 from by omega]

theorem active_of_test (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n) (actual : RoundState source p roots n index)
    (word : BitVec 64) (read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) withdrawalTest=some (.val (.word word))) (nonzero : word≠0) : index<n := by
  have expected := test_read source p roots n index bounded inside actual
  by_cases active : index<n
  · exact active
  rw [if_neg active] at expected
  have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact False.elim (nonzero zero)

def valid (p roots : BitVec 64) (n : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  ∃ index : Nat,index≤n ∧ RoundState source p roots n index

def remaining (n : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  760*(n-(CounterFlow.counterWord source (ofString "i")).toNat)

theorem remaining_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n) (actual : RoundState source p roots n index) :
    remaining n source=760*(n-index) := by
  have number : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [remaining,CounterFlow.counterWord,actual.position,valueWord,number]

theorem allowance_step (price n index : Nat) (active : index<n) : price*(n-index)=price+price*(n-(index+1)) := by
  have distance : n-index=(n-(index+1))+1 := by omega
  rw [distance,Nat.mul_add,Nat.mul_one,Nat.add_comm]
/-- Current literal withdrawal loop, including all same non-timeout failures:
758 body ticks, one call tick and one loop tick per actual record. -/
theorem loop_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n) (actual : RoundState source p roots n index)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source withdrawalLoop=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤760*(n-index) := by
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → valid p roots n current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) withdrawalTest=some (.val (.word word)) → word≠0 → current.clock≠0 →
      let output:=evaluateHOLFiniteState (decClockHOLFinite current) withdrawalStep
      output.1≠some .timeOut → current.clock-output.2.clock≤remaining n current ∧
        ((output.1=none ∨ output.1=some .continue) → valid p roots n output.2 ∧
          current.clock-output.2.clock+remaining n output.2≤remaining n current) := by
    intro current codeEq currentValid word read nonzero funded
    obtain ⟨position,positionBound,ready⟩ := currentValid
    have active := active_of_test current p roots n position bounded positionBound ready word read nonzero
    let output := evaluateHOLFiniteState (decClockHOLFinite current) withdrawalStep
    dsimp only
    intro bodyNotTimeout
    have currentAllowance := remaining_read current p roots n position bounded positionBound ready
    have bodyPrice := step_cost (decClockHOLFinite current) output.2 p roots n position
      ready.dec_clock output.1 rfl bodyNotTimeout
    change current.clock-1-output.2.clock≤759 at bodyPrice
    have bodyClock := evaluateHOLFiniteState_clock_le (decClockHOLFinite current) withdrawalStep
    change output.2.clock≤current.clock-1 at bodyClock
    have amortized := allowance_step 760 n position active
    have stopped : current.clock-output.2.clock≤remaining n current := by rw [currentAllowance]; omega
    refine ⟨stopped,?_⟩
    intro continuing
    have summary := (withdrawal_step_local (ofString "wd") (by decide)).summary_full (decClockHOLFinite current)
    unfold LocalSummary at summary
    have normal : output.1=none := continuing.resolve_right summary.2.2.2
    have bodyRun : evaluateHOLFiniteState (decClockHOLFinite current) withdrawalStep=(none,output.2) := Prod.ext normal rfl
    have next := step_normal (decClockHOLFinite current) output.2 p roots n position
      ready.dec_clock bodyRun
    have nextBound : position+1≤n := by omega
    have nextAllowance := remaining_read output.2 p roots n (position+1) bounded nextBound next
    refine ⟨⟨position+1,nextBound,next⟩,?_⟩
    change current.clock-output.2.clock+remaining n output.2≤remaining n current
    rw [currentAllowance,nextAllowance]
    omega
  have observed : (evaluateHOLFiniteState source (.while withdrawalTest withdrawalStep)).1≠some .timeOut := by rw [←loop_shapes.2.2.1,run]; exact notTimeout
  have price := ClockCost.potential_loop_terminating source.code withdrawalTest withdrawalStep (valid p roots n) (remaining n) priced source rfl ⟨index,inside,actual⟩ observed
  rw [←loop_shapes.2.2.1] at price
  change source.clock-(evaluateHOLFiniteState source withdrawalLoop).2.clock≤remaining n source at price
  rw [run,remaining_read source p roots n index bounded inside actual] at price
  exact price

/-- The same real normal withdrawalLoop exit retains the actual bounded counter,
current caller word bindings; no future withdrawalLoop outcome is supplied. -/
theorem loop_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n) (actual : RoundState source p roots n index)
    (run : evaluateHOLFiniteState source withdrawalLoop=(none,post)) : valid p roots n post := by
  have transition : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → valid p roots n current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) withdrawalTest=some (.val (.word word)) → word≠0 → current.clock≠0 → ∀ target,
      evaluateHOLFiniteState (decClockHOLFinite current) withdrawalStep=(none,target) → valid p roots n target := by
    intro current codeEq currentValid word read nonzero funded target bodyRun
    obtain ⟨position,positionBound,ready⟩ := currentValid
    have active := active_of_test current p roots n position bounded positionBound ready word read nonzero
    have next := step_normal (decClockHOLFinite current) target p roots n position
      ready.dec_clock bodyRun
    exact ⟨position+1,by omega,next⟩
  rw [loop_shapes.2.2.1] at run
  exact loop_invariant source.code (ofString "wd") withdrawalTest withdrawalStep (withdrawal_step_local (ofString "wd") (by decide))
    (valid p roots n) transition source post rfl ⟨index,inside,actual⟩ run

end InitECandidate.Solver.Input.CurrentHash.PayloadHash.Withdrawals

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Withdrawals.arguments_read
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Withdrawals.step_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Withdrawals.step_normal
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Withdrawals.test_read
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Withdrawals.active_of_test
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Withdrawals.remaining_read
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Withdrawals.allowance_step
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Withdrawals.loop_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Withdrawals.loop_normal
