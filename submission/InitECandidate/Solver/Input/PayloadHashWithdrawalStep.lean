import InitECandidate.Solver.Input.PayloadHashWithdrawals
import InitECandidate.Solver.Input.ClockCostTerminatingSequence
import InitECandidate.Solver.Input.CounterLoopCost

namespace InitECandidate.Solver.Input.PayloadHash.Withdrawals
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem step_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (actual : RoundState source p roots cursor stp accel chunk zeros n index) (geometry : Geometry p roots cursor n) (active : index<n)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source withdrawalStep=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤616 := by
  rw [loop_shapes.2.2.2] at run
  exact ClockCost.sequence_terminating source post _ increment 616 0
    (fun observed target evaluated notTimeout=>(call_summary source target p roots cursor stp accel chunk zeros n index actual geometry active observed evaluated notTimeout).1)
    (by intro middle normal observed target evaluated notTimeout
        have zero:=ClockCost.assign middle.code (ofString "i") (.op .add [localVar "i",.const 1#64]) middle rfl
        change middle.clock-(evaluateHOLFiniteState middle increment).2.clock≤0 at zero
        rw [evaluated] at zero
        exact zero)
    result run notTimeout

theorem step_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (actual : RoundState source p roots cursor stp accel chunk zeros n index) (geometry : Geometry p roots cursor n) (active : index<n)
    (run : evaluateHOLFiniteState source withdrawalStep=(none,post)) : RoundState post p roots cursor stp accel chunk zeros n (index+1) := by
  rw [loop_shapes.2.2.2] at run
  obtain ⟨middle,called,advanced⟩ := sequence_none source post _ increment run
  have current := (call_summary source middle p roots cursor stp accel chunk zeros n index actual geometry active none called (by simp)).2 rfl
  have read : eval middle (.op .add [localVar "i",.const 1#64])=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,current.position,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  have endpoint := assign_none middle post "i" (.op .add [localVar "i",.const 1#64]) (BitVec.ofNat 64 (index+1)) read advanced
  rw [endpoint]
  exact ⟨SszHash.Workspace.of_fields middle _ stp accel chunk zeros current.workspace rfl rfl (by intro key different; rfl),
    (bind_lookup_other middle "i" "wd" _ (by decide)).trans current.pointer,
    (bind_lookup_other middle "i" "nwd" _ (by decide)).trans current.count,
    (bind_lookup_other middle "i" "roots" _ (by decide)).trans current.rootsLocal,bind_lookup_same _ _ _,current.heap⟩

theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n) (actual : RoundState source p roots cursor stp accel chunk zeros n index) :
    evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) withdrawalTest=some (.val (.word (if index<n then 1#64 else 0#64))) := by
  have iNumber : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have nNumber : (BitVec.ofNat 64 n).toNat=n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [evalHOLFinite,evalHOLExact,toExact,withdrawalTest,localVar,actual.position,actual.count,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,iNumber,nNumber,
    show index<9223372036854775808 from by omega,show n<9223372036854775808 from by omega]

theorem active_of_test (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n) (actual : RoundState source p roots cursor stp accel chunk zeros n index)
    (word : BitVec 64) (read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) withdrawalTest=some (.val (.word word))) (nonzero : word≠0) : index<n := by
  have expected := test_read source p roots cursor stp accel chunk zeros n index bounded inside actual
  by_contra inactive
  rw [if_neg inactive] at expected
  have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero zero

def valid (p roots cursor stp accel chunk zeros : BitVec 64) (n : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  ∃ index : Nat,index≤n ∧ RoundState source p roots cursor stp accel chunk zeros n index

def remaining (n : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) := 617*(n-(CounterFlow.counterWord source (ofString "i")).toNat)

theorem remaining_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n) (actual : RoundState source p roots cursor stp accel chunk zeros n index) : remaining n source=617*(n-index) := by
  have number : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp only [remaining,CounterFlow.counterWord,actual.position,Option.getD_some,valueWord,number]

end InitECandidate.Solver.Input.PayloadHash.Withdrawals

#print axioms InitECandidate.Solver.Input.PayloadHash.Withdrawals.step_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.Withdrawals.step_normal
#print axioms InitECandidate.Solver.Input.PayloadHash.Withdrawals.test_read
#print axioms InitECandidate.Solver.Input.PayloadHash.Withdrawals.active_of_test
#print axioms InitECandidate.Solver.Input.PayloadHash.Withdrawals.remaining_read
