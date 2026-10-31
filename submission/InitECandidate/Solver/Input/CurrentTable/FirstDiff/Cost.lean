import InitECandidate.Solver.Input.CurrentTable.FirstDiff.Program
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.ScopedCallClassified
import InitECandidate.Solver.Input.ReturnFactsScalar
import InitECandidate.Solver.Input.ReturnFactsLoop
import InitECandidate.Solver.Input.ClockCostCurrentValue
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Input.CurrentTable.FirstDiff
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Flapjack.Compiler.Encoders.Asm

/-- The real signed inner counter starts at zero, remains nonnegative and
can run at most eight bit tests, including early returns and short clocks. -/
theorem different_cost (code) : ClockCost.Bound code different 8 := by
  intro source installed
  rw [shapes.2.2.2.2.2.2.1]
  apply ClockCost.declared_value_current source _ _ _ (.val (.word 0#64)) bitLoop 8
  · simp [eval,evalHOLExact]
  · let entry := setVarHOLFinite (ofString "j") (.val (.word 0#64)) source
    change entry.clock - (evaluateHOLFiniteState entry bitLoop).2.clock ≤ 8
    rw [shapes.2.2.2.2.2.2.2.1]
    have cost := CounterFlow.loop_snapshot_cost code (ofString "j") (ofString "x")
      (entry.locals.lookup (ofString "x")) bitLimit bitStep 0 8 (by decide)
      (by
        intro current word currentCell saved bounded
        have small : word.toNat < 9223372036854775808 := by omega
        simp [bitLimit,localVar,evalHOLFinite,evalHOLExact,currentCell,wordCmpHOL,
          holAsmSignedLess,small])
      (ClockCost.of_quiet code bitStep (bit_quiet code)) bit_advance (bit_flow _ (by decide))
      entry 0#64 installed
      (by simp [entry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]) rfl (by decide)
    simpa using cost

theorem step_cost (code) : ClockCost.Bound code step 8 := by
  rw [shapes.2.2.2.1,shapes.2.2.2.2.1,shapes.2.2.2.2.2.1]
  apply ClockCost.declared code _ _ _ _ 8
  have choicePrice := ClockCost.conditional code (.cmp .notEqual (localVar "x") (.const 0#64))
    different .skip 8 0 (different_cost code) (ClockCost.skip code)
  have price := ClockCost.sequence code _ (increment "i") 8 0 (by simpa using choicePrice)
    (ClockCost.assign code _ _)
  simpa using price

/-- No mapped byte contents or successful future reads are assumed. Every
actual outcome of the unchanged scan is charged, at any entering clock. -/
theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (length : Nat) (word : BitVec 64) (small : length < 2^64)
    (counterCell : source.locals.lookup (ofString "i") = some (.val (.word word)))
    (lengthCell : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 length))))
    (initial : word.toNat ≤ length) :
    source.clock - (evaluateHOLFiniteState source loop).2.clock ≤ 9 * (length - word.toNat) := by
  rw [shapes.2.2.1]
  exact CounterFlow.loop_snapshot_cost source.code (ofString "i") (ofString "key_len")
    (some (.val (.word (BitVec.ofNat 64 length)))) test step 8 length small
    (by
      intro current number currentCell saved bounded
      have lengthMod : length % 18446744073709551616 = length := Nat.mod_eq_of_lt small
      simp [test,localVar,evalHOLFinite,evalHOLExact,currentCell,saved,wordCmpHOL,
        BitVec.lt_def,BitVec.toNat_ofNat,lengthMod])
    (step_cost source.code) step_advance (step_flow _ (by decide) (by decide) (by decide))
    source word rfl counterCell lengthCell initial

/-- Actual htab_first_diff body allowance. In the current database callers,
length32 gives288source ticks; straight-line target work remains separate. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (length : Nat) (small : length < 2^64)
    (lengthCell : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock - (evaluateHOLFiniteState source body).2.clock ≤ 9 * length := by
  rw [shapes.1]
  apply ClockCost.declared_value_current source _ _ _ (.val (.word 0#64)) afterI _
  · simp [eval,evalHOLExact]
  · let entry := setVarHOLFinite (ofString "i") (.val (.word 0#64)) source
    change entry.clock - (evaluateHOLFiniteState entry afterI).2.clock ≤ 9 * length
    have currentCell : entry.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
      simp [entry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    have saved : entry.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 length))) := by
      simpa [entry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
        show ofString "i" ≠ ofString "key_len" from by decide] using lengthCell
    have price := loop_cost entry length 0#64 small currentCell saved (by simp)
    rw [shapes.2.1]
    have result := ClockCost.sequence_reached_current entry loop (.return (.panop .mul [localVar "key_len",.const 8#64])) (9 * length) 0
      (by simpa using price) (by intro middle run; exact ClockCost.returned middle.code _ middle rfl)
    simpa using result

end InitECandidate.Solver.Input.CurrentTable.FirstDiff

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.different_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.loop_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.body_cost

namespace InitECandidate.Solver.Input.CurrentTable.FirstDiff
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Flapjack.Compiler.Encoders.Asm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- A real returned position is bounded by the current scalar key width.
This property needs no key-byte view or successful future memory read. -/
def ScalarAnswer (length : Nat) (value : ValueHOL 64) : Prop :=
  ∃ position : Nat,position≤8*length ∧ value=.val (.word (BitVec.ofNat 64 position))

theorem scalar_bit_limit_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (digit : Nat) (bounded : digit≤8)
    (cell : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 digit)))) :
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) bitLimit=
      some (.val (.word (if digit<8 then 1#64 else 0#64))) := by
  have number : (BitVec.ofNat 64 digit).toNat=digit:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [bitLimit,evalHOLFinite,evalHOLExact,toExact,localVar,cell,wordCmpHOL,holAsmSignedLess,number,show ¬9223372036854775808≤digit from by omega]

theorem scalar_byte_limit_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index length : Nat)
    (small : length≤60) (bounded : index≤length)
    (cell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (lengthCell : source.locals.lookup (ofString "key_len")=some (.val (.word (BitVec.ofNat 64 length)))) :
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=
      some (.val (.word (if index<length then 1#64 else 0#64))) := by
  have indexNumber : (BitVec.ofNat 64 index).toNat=index:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have lengthNumber : (BitVec.ofNat 64 length).toNat=length:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [test,evalHOLFinite,evalHOLExact,toExact,localVar,cell,lengthCell,wordCmpHOL,BitVec.lt_def,indexNumber,lengthNumber]

/-- The real inner scan's counter starts at0, advances only on an actual
continuation, and every returning digit is below8. -/
theorem scalar_different_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index length : Nat)
    (small : length≤60) (inside : index<length)
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    ReturnFacts.Returns source different (ScalarAnswer length) := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ digit : Nat,digit≤8 ∧
    current.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) ∧
    current.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 digit)))
  have active (current : PanSemStateFiniteExact 64 Guest.HostMemory) (digit : Nat) (bounded : digit≤8)
      (cell : current.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 digit)))) (observed : BitVec 64)
      (read : evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) bitLimit=some (.val (.word observed)))
      (nonzero : observed≠0#64) : digit<8:=by
    have expected:=scalar_bit_limit_read current digit bounded cell
    by_contra inactive
    rw [if_neg inactive] at expected
    have same : observed=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
    exact nonzero same
  have returned : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ observed,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) bitLimit=some (.val (.word observed)) →
      observed≠0#64 → current.clock≠0 → ReturnFacts.Returns (decClockHOLFinite current) bitStep (ScalarAnswer length):=by
    intro current codeEq state observed read nonzero funded
    obtain ⟨digit,bounded,iCell,jCell⟩:=state
    have live:=active current digit bounded jCell observed read nonzero
    let entry:=decClockHOLFinite current
    have iNow : entry.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))):=iCell
    have jNow : entry.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 digit))):=jCell
    have resultRead : eval entry bitResult=some (.val (.word (BitVec.ofNat 64 (index*8+digit)))):=by
      simp [bitResult,eval,evalHOLExact,evalListHOLExact,localVar,iNow,jNow,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
        BitVec.ofNat_add,BitVec.ofNat_mul]
    rw [shapes.2.2.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.2.2]
    apply ReturnFacts.sequence
    · apply ReturnFacts.conditional
      · exact ReturnFacts.returned entry bitResult _ (ScalarAnswer length) resultRead ⟨index*8+digit,by omega,rfl⟩
      · exact ReturnFacts.skip _ _
    · intro middle continued
      exact ReturnFacts.local_prefix middle (ofString "i") (increment "j") (.assign _ _ (by decide)) _
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ observed,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) bitLimit=some (.val (.word observed)) →
      observed≠0#64 → current.clock≠0 → ∀ target result,
      evaluateHOLFiniteState (decClockHOLFinite current) bitStep=(result,target) →
      (result=none ∨ result=some .continue) → invariant target:=by
    intro current codeEq state observed read nonzero funded target result run continuing
    obtain ⟨digit,bounded,iCell,jCell⟩:=state
    have live:=active current digit bounded jCell observed read nonzero
    have flow:=bit_flow (ofString "i") (by decide)
    have normalResult : result=none:=by
      rcases continuing with normal|continued
      · exact normal
      · have impossible:=(flow.summary (decClockHOLFinite current)).2.2
        rw [run] at impossible
        exact (impossible continued).elim
    have normal : evaluateHOLFiniteState (decClockHOLFinite current) bitStep=(none,target):=by simpa only [normalResult] using run
    have next:=bit_advance (decClockHOLFinite current) target (BitVec.ofNat 64 digit) jCell normal
    exact ⟨digit+1,by omega,(flow.none_preserves _ _ normal).trans iCell,by simpa only [BitVec.ofNat_add] using next⟩
  rw [shapes.2.2.2.2.2.2.1]
  apply ReturnFacts.declared_word source "j" (.const 0#64) 0#64 bitLoop (ScalarAnswer length) rfl
  rw [shapes.2.2.2.2.2.2.2.1]
  exact ReturnFacts.loop source.code bitLimit bitStep invariant (ScalarAnswer length) returned progress (bind source "j" 0#64) rfl
    ⟨0,by decide,(bind_lookup_other source "j" "i" 0#64 (by decide)).trans indexCell,bind_lookup_same _ _ _⟩

/-- Scalar first-difference positions are derived solely from the real
bounded counters, including returns after any successful byte comparison. -/
theorem scalar_body_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) (small : length≤60)
    (lengthCell : source.locals.lookup (ofString "key_len")=some (.val (.word (BitVec.ofNat 64 length)))) :
    ReturnFacts.Returns source body (ScalarAnswer length) := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ index : Nat,index≤length ∧
    current.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) ∧
    current.locals.lookup (ofString "key_len")=some (.val (.word (BitVec.ofNat 64 length)))
  have active (current : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) (bounded : index≤length)
      (iCell : current.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
      (nCell : current.locals.lookup (ofString "key_len")=some (.val (.word (BitVec.ofNat 64 length)))) (observed : BitVec 64)
      (read : evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word observed)))
      (nonzero : observed≠0#64) : index<length:=by
    have expected:=scalar_byte_limit_read current index length small bounded iCell nCell
    by_contra inactive
    rw [if_neg inactive] at expected
    have same : observed=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
    exact nonzero same
  have returned : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ observed,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word observed)) →
      observed≠0#64 → current.clock≠0 → ReturnFacts.Returns (decClockHOLFinite current) step (ScalarAnswer length):=by
    intro current codeEq state observed read nonzero funded
    obtain ⟨index,bounded,iCell,nCell⟩:=state
    have live:=active current index bounded iCell nCell observed read nonzero
    rw [shapes.2.2.2.1]
    apply ReturnFacts.declared
    intro value
    let entry:=setVarHOLFinite (ofString "x") value (decClockHOLFinite current)
    have iNow : entry.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))):=by
      simpa [entry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,decClockHOLFinite,
        show ofString "x"≠ofString "i" from by decide] using iCell
    rw [shapes.2.2.2.2.1,shapes.2.2.2.2.2.1]
    apply ReturnFacts.sequence
    · apply ReturnFacts.conditional
      · exact scalar_different_returns entry index length small live iNow
      · exact ReturnFacts.skip _ _
    · intro middle continued
      exact ReturnFacts.local_prefix middle (ofString "x") (increment "i") (.assign _ _ (by decide)) _
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ observed,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word observed)) →
      observed≠0#64 → current.clock≠0 → ∀ target result,
      evaluateHOLFiniteState (decClockHOLFinite current) step=(result,target) →
      (result=none ∨ result=some .continue) → invariant target:=by
    intro current codeEq state observed read nonzero funded target result run continuing
    obtain ⟨index,bounded,iCell,nCell⟩:=state
    have live:=active current index bounded iCell nCell observed read nonzero
    have flow:=step_flow (ofString "key_len") (by decide) (by decide) (by decide)
    have normalResult : result=none:=by
      rcases continuing with normal|continued
      · exact normal
      · have impossible:=(flow.summary (decClockHOLFinite current)).2.2
        rw [run] at impossible
        exact (impossible continued).elim
    have normal : evaluateHOLFiniteState (decClockHOLFinite current) step=(none,target):=by simpa only [normalResult] using run
    have next:=step_advance (decClockHOLFinite current) target (BitVec.ofNat 64 index) iCell normal
    exact ⟨index+1,by omega,by simpa only [BitVec.ofNat_add] using next,(flow.none_preserves _ _ normal).trans nCell⟩
  rw [shapes.1]
  apply ReturnFacts.declared_word source "i" (.const 0#64) 0#64 afterI (ScalarAnswer length) rfl
  let entry:=bind source "i" 0#64
  have nCell : entry.locals.lookup (ofString "key_len")=some (.val (.word (BitVec.ofNat 64 length))):=
    (bind_lookup_other source "i" "key_len" 0#64 (by decide)).trans lengthCell
  have valid : invariant entry:=⟨0,by omega,bind_lookup_same _ _ _,nCell⟩
  rw [shapes.2.1]
  apply ReturnFacts.sequence
  · rw [shapes.2.2.1]
    exact ReturnFacts.loop source.code test step invariant (ScalarAnswer length) returned progress entry rfl valid
  · intro middle completed
    have flow : LocalFlow (ofString "key_len") loop:=by
      rw [shapes.2.2.1]
      exact .loop test (step_flow _ (by decide) (by decide) (by decide))
    have currentLength:=(flow.none_preserves entry middle completed).trans nCell
    apply ReturnFacts.returned middle _ (.val (.word (BitVec.ofNat 64 (8*length)))) (ScalarAnswer length)
    · simp [eval,evalHOLExact,evalListHOLExact,localVar,currentLength,valueIsWord,valueWord,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]
    · exact ⟨8*length,Nat.le_refl _,rfl⟩

/-- The actual variable-width caller stops within9*length+1 ticks or
resumes with its own bounded returned position and the full memory frame. -/
theorem scoped_scalar_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (a b : BitVec 64) (length : Nat) (small : length≤60) (installed : OriginalCode.Installed source.code)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word a),.val (.word b),.val (.word (BitVec.ofNat 64 length))])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_first_diff") arguments continuation)=(outcome,post)) :
    (source.clock-post.clock≤9*length+1 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ target inner position,position≤8*length ∧ LocalEffects.erase target=LocalEffects.erase source ∧
        target.clock≤source.clock ∧ source.clock-target.clock≤9*length+1 ∧
        evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word (BitVec.ofNat 64 position)))) continuation=(outcome,inner) ∧
        post=restore source name inner := by
  obtain ⟨callee,called,aCell,bCell,lengthCell⟩:=word_triple_environment source.code.lookup (ofString "htab_first_diff")
    (ofString "a") (ofString "b") (ofString "key_len") body .one a b (BitVec.ofNat 64 length)
    (by decide) (by decide) (by decide) (original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have price:=body_cost entry length (by omega) lengthCell
  rcases CallNormal.scoped_classified source post name .one (ofString "htab_first_diff") arguments _ body continuation callee .one (9*length)
    args called price outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩:=reached
    obtain ⟨position,bounded,answer⟩:=scalar_body_returns entry length small lengthCell target value bodyRun
    have frame:=readonly source.code entry rfl
    rw [bodyRun] at frame
    rw [answer] at continued
    exact Or.inr ⟨target,inner,position,bounded,frame,forward,cost,continued,endpoint⟩

end InitECandidate.Solver.Input.CurrentTable.FirstDiff

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.scalar_bit_limit_read
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.scalar_byte_limit_read
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.scalar_different_returns
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.scalar_body_returns

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.scoped_scalar_trace
