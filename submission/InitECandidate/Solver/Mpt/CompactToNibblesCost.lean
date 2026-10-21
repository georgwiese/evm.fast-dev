import InitECandidate.Solver.Mpt.CompactToNibblesByteTrace
import InitECandidate.Solver.Mpt.CompactToNibblesSuffixCost
import InitECandidate.Solver.Mpt.FailGuard
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem allocation_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer odd : BitVec 64) (length : Nat)
    (positive : 1≤length) (small : length+4<2^64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (oddCell : source.locals.lookup (ofString "odd")=some (.val (.word odd)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source allocationCall).2.clock≤length/4+6 := by
  let request:=2#64*BitVec.ofNat 64 length
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [amount]=some (PersistentAlloc.values request):=by
    simp [amount,PersistentAlloc.values,request,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,lengthCell,panOpHOL,valueIsWord,valueWord]
  obtain ⟨callee,called,amountCell⟩:=PersistentAlloc.environment source.code.lookup request (PersistentAlloc.original_code source.code installed)
  have price:=PersistentAlloc.body_price source.code installed (callEntryStateHOLFinite source callee) rfl
  rw [allocation_shape]
  have full:=Input.ClockCost.scoped_reached_current source "out" .one (ofString "alloc") [amount] _ PersistentAlloc.body afterAllocation callee .one 1 (length/4+4)
    args called price (by
      intro target returned bodyRun checked
      have typed : shapeOfHOLExact returned=.one:=(shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1
      have scalar : ∃ word : BitVec 64,returned=.val (.word word):=by
        cases returned with
        | val payload=>cases payload with | word word=>exact ⟨word,rfl⟩
        | rStruct fields=>simp only [shapeOfHOLExact] at typed; cases typed
        | nStruct name fields=>simp only [shapeOfHOLExact] at typed; cases typed
      obtain ⟨out,returnedEq⟩:=scalar
      subst returned
      let ready:=Input.CallNormal.continuationEntry source target "out" (.val (.word out))
      have currentPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)):=
        (Input.CallNormal.continuation_lookup_other source target "out" "p" _ (by decide)).trans pointerCell
      have currentLength : ready.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=
        (Input.CallNormal.continuation_lookup_other source target "out" "n" _ (by decide)).trans lengthCell
      have currentOdd : ready.locals.lookup (ofString "odd")=some (.val (.word odd)):=
        (Input.CallNormal.continuation_lookup_other source target "out" "odd" _ (by decide)).trans oddCell
      have currentOut : ready.locals.lookup (ofString "out")=some (.val (.word out)):=Input.CallNormal.continuation_lookup_same _ _ _ _
      have codeEq:=(Input.evaluation_fields (callEntryStateHOLFinite source callee) target PersistentAlloc.body (some (.returned (.val (.word out)))) bodyRun).2.2.2
      have currentInstalled : Input.OriginalCode.Installed ready.code:=by change Input.OriginalCode.Installed target.code; rw [codeEq]; exact installed
      exact after_allocation_cost ready pointer out odd length positive small currentPointer currentLength currentOut currentOdd currentInstalled)
  exact full.trans (by omega)

theorem after_guard_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (length : Nat)
    (positive : 1≤length) (small : length+4<2^64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterGuard).2.clock≤length/4+6 := by
  let output:=evaluateHOLFiniteState source afterGuard
  rcases allocation_entry_trace source output.2 pointer pointerCell output.1 rfl with stopped|reached
  · exact stopped.trans (by omega)
  · obtain ⟨byte,restoreStack,inner,setup,continued,endpoint,clock⟩:=reached
    let byteState:=QueryBranch.bind source "c0" (BitVec.ofNat 64 byte.toNat)
    let current:=prepared byteState (BitVec.ofNat 64 byte.toNat)
    have currentPointer : current.locals.lookup (ofString "p")=some (.val (.word pointer)):=
      (prepared_other byteState _ "p" (by decide) (by decide) (by decide)).trans ((bind_lookup_other source "c0" "p" _ (by decide)).trans pointerCell)
    have currentLength : current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=
      (prepared_other byteState _ "n" (by decide) (by decide) (by decide)).trans ((bind_lookup_other source "c0" "n" _ (by decide)).trans lengthCell)
    have currentOdd : current.locals.lookup (ofString "odd")=some (.val (.word ((BitVec.ofNat 64 byte.toNat>>>4)&&&1#64))):=bind_lookup_same _ _ _
    have price:=allocation_cost current pointer _ length positive small currentPointer currentLength currentOdd installed
    rw [continued] at price
    change source.clock-inner.clock≤length/4+6 at price
    change source.clock-output.2.clock≤length/4+6
    rw [clock]
    exact price

/-- Complete unchanged original225, including an empty path, arbitrary
first-byte read, actual heap allocation and generic nibble conversion.
This all-outcome source-clock bound needs only the real scalar inputs/code. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (length : Nat)
    (small : length+4<2^64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤length/4+6 := by
  rw [body_shape]
  have price:=Fail.guard_reached_cost source zeroTest 5#64 afterGuard (length/4+6) installed (by
    intro passed
    have test:=(Fail.guard_normal source source zeroTest [.const 5#64] installed passed).1
    have positive : 1≤length:=by
      by_contra bad
      have zero : length=0:=by omega
      have actual : eval source zeroTest=some (.val (.word 1#64)):=by
        simp [eval,zeroTest,evalHOLExact,localVar,toExact,lengthCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      have impossible : (1#64 : BitVec 64)=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actual.symm.trans test
      exact (by decide : (1#64 : BitVec 64)≠0#64) impossible
    exact after_guard_cost source pointer length positive small pointerCell lengthCell installed)
  exact price.trans (by omega)

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.allocation_cost
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.after_guard_cost
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.body_cost
