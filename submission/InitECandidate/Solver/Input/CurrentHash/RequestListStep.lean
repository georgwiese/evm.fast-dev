import InitECandidate.Solver.Input.CurrentHash.RequestListBranches
import InitECandidate.Solver.Input.CounterLoopCost

namespace InitECandidate.Solver.Input.CurrentHash.RequestList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem RoundState.dec_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out : BitVec 64) (n index : Nat)
    (actual : RoundState source kind p roots out n index) : RoundState (decClockHOLFinite source) kind p roots out n index :=
  ⟨actual.installed,
    actual.category,actual.pointer,actual.count,actual.size,actual.root,actual.output,actual.position⟩

theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n) (actual : RoundState source kind p roots out n index) :
    evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) test=some (.val (.word (if index<n then 1#64 else 0#64))) := by
  have iNumber : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have nNumber : (BitVec.ofNat 64 n).toNat=n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [evalHOLFinite,evalHOLExact,toExact,test,localVar,actual.position,actual.count,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,iNumber,nNumber,
    show index<9223372036854775808 from by omega,show n<9223372036854775808 from by omega]

theorem active_of_test (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n) (actual : RoundState source kind p roots out n index)
    (word : BitVec 64) (read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) test=some (.val (.word word))) (nonzero : word≠0) : index<n := by
  have expected := test_read source kind p roots out n index bounded inside actual
  by_cases active : index<n
  · exact active
  rw [if_neg active] at expected
  have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact False.elim (nonzero zero)

/-- Genuine normal dispatch plus increment advances one actual record,
retains the loop's actual caller inputs and installed code. -/
theorem step_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out : BitVec 64) (n index : Nat)
    (_active : index<n) (actual : RoundState source kind p roots out n index)
    (run : evaluateHOLFiniteState source step=(none,post)) : RoundState post kind p roots out n (index+1) := by
  have nextCode : OriginalCode.Installed post.code := by
    rw [(evaluation_fields source post _ none run).2.2.2]
    exact actual.installed
  have other (name : String) (different : ofString name≠ofString "i") : post.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    have summary : LocalSummary (ofString name) step source := (chain_local (ofString name) kinds different).summary_full source
    unfold LocalSummary at summary
    rw [run] at summary
    exact summary.1 rfl
  have position : post.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
    simpa only [BitVec.ofNat_add] using chain_advance kinds source post (BitVec.ofNat 64 index) actual.position run
  exact ⟨nextCode,(other "kind" (by decide)).trans actual.category,(other "p" (by decide)).trans actual.pointer,(other "n" (by decide)).trans actual.count,
    (other "sz" (by decide)).trans actual.size,(other "roots" (by decide)).trans actual.root,(other "out" (by decide)).trans actual.output,position⟩

def valid (kind : Kind) (p roots out : BitVec 64) (n : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  ∃ index : Nat,index≤n ∧ RoundState source kind p roots out n index

def remaining (kind : Kind) (n : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  (kind.record.price+2)*(n-(CounterFlow.counterWord source (ofString "i")).toNat)

theorem remaining_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n) (actual : RoundState source kind p roots out n index) :
    remaining kind n source=(kind.record.price+2)*(n-index) := by
  have number : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [remaining,CounterFlow.counterWord,actual.position,valueWord,number]

theorem allowance_step (price n index : Nat) (active : index<n) : price*(n-index)=price+price*(n-(index+1)) := by
  have distance : n-index=(n-(index+1))+1 := by omega
  rw [distance,Nat.mul_add,Nat.mul_one,Nat.add_comm]

end InitECandidate.Solver.Input.CurrentHash.RequestList

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.RoundState.dec_clock
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.test_read
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.active_of_test
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.step_normal
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.remaining_read
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.allowance_step
