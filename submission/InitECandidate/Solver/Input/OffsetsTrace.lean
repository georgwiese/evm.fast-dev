import InitECandidate.Solver.Input.OffsetsCall
import InitECandidate.Solver.Input.TerminatingPaddedSequence

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual enclosing non-timeout run funds the validator's actual cost,
not its larger worst-case allowance. Every mapped <=8-word array either
resumes with derived validity or stops with its real decoder exception. -/
theorem call_trace {F : Type} (source post : PanSemStateFiniteExact 64 F) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (pointer fixed total : BitVec 64) (offsets : Nat → BitVec 64) (count : Nat) (positive : 0 < count) (small : count ≤ 8)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some (arguments pointer fixed total count))
    (code : source.code.lookup (ofString "ssz_check_offsets") = some (formals,body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail") = some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (mapped : ∀ position < count,source.memaddrs (pointer + BitVec.ofNat 64 (8 * position)))
    (cells : ∀ position < count,source.memory (pointer + BitVec.ofNat 64 (8 * position)) = .word (offsets position))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.seq (.call (some (none,none)) (ofString "ssz_check_offsets") expressions) continuation) = (result,post))
    (notTimeout : result ≠ some .timeOut) :
    ∃ middle paid,paid ≤ count + 2 ∧ paid ≤ source.clock ∧ middle.clock = source.clock - paid ∧
      ((evaluateHOLFiniteState source (.call (some (none,none)) (ofString "ssz_check_offsets") expressions) = (none,middle) ∧
        middle = {source with clock := source.clock - paid} ∧ offsets 0 = fixed ∧ (∀ position < count,ValidAt fixed total offsets position) ∧
        evaluateHOLFiniteState middle continuation = (result,post)) ∨
       ∃ error : BitVec 64,(error = 10#64 ∨ error = 11#64 ∨ error = 12#64) ∧
        evaluateHOLFiniteState source (.call (some (none,none)) (ofString "ssz_check_offsets") expressions) = (some (.exception (ofString "SszErr") (.val (.word error))),middle) ∧
        result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ post = middle) := by
  classical
  let padding := count + 2
  let padded := {source with clock := source.clock + padding}
  have paddedArgs : evalListHOLFinite padded (h := fun address => Classical.propDecidable (padded.memaddrs address)) expressions = some (arguments pointer fixed total count) := by
    change evalListHOLExact (stateAddClock source.toExact padding) expressions = _
    rw [evalListHOLExact_stateAddClock]
    exact args
  obtain ⟨prefixResult,paddedPost,paid,prefixRun,bound,frame,outcome⟩ := call_execute padded expressions pointer fixed total offsets count positive small paddedArgs code failCode exceptionShape mapped cells (by change count + 2 ≤ source.clock + (count + 2); omega)
  obtain ⟨funded,actual⟩ := terminating_padded_sequence source post paddedPost _ continuation padding prefixResult result prefixRun run notTimeout
  let middle := {paddedPost with clock := paddedPost.clock - padding}
  have paddedClock : paddedPost.clock = source.clock + padding - paid := by
    have projected := congrArg (fun state : PanSemStateFiniteExact 64 F => state.clock) frame
    exact projected
  have enough : paid ≤ source.clock := by rw [paddedClock] at funded; omega
  have middleClock : middle.clock = source.clock - paid := by change paddedPost.clock - padding = _; rw [paddedClock]; omega
  have middleFrame : emptyLocalsHOLFinite middle = emptyLocalsHOLFinite {source with clock := source.clock - paid} := by
    change {emptyLocalsHOLFinite paddedPost with clock := middle.clock} = _
    rw [frame,middleClock]
    rfl
  refine ⟨middle,paid,bound,enough,middleClock,?_⟩
  rcases outcome with normal | fault
  · obtain ⟨rfl,first,locals,valid⟩ := normal
    have localEq : middle.locals = source.locals := locals
    have wholeEq := congrArg (fun state : PanSemStateFiniteExact 64 F => {state with locals := middle.locals}) middleFrame
    have middleEq : middle = {source with clock := source.clock - paid} := by
      have full : middle = {{source with clock := source.clock - paid} with locals := middle.locals} := by
        simpa only [emptyLocalsHOLFinite] using wholeEq
      rw [localEq] at full
      exact full
    have callRun : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "ssz_check_offsets") expressions) = (none,middle) := actual
    rw [evaluateHOLFiniteState_seq_line780,callRun] at run
    exact Or.inl ⟨callRun,middleEq,first,valid,run⟩
  · obtain ⟨error,allowed,rfl⟩ := fault
    have callRun : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "ssz_check_offsets") expressions) = (some (.exception (ofString "SszErr") (.val (.word error))),middle) := actual
    rw [evaluateHOLFiniteState_seq_line780,callRun] at run
    have results := congrArg Prod.fst run
    have states := congrArg Prod.snd run
    exact Or.inr ⟨error,allowed,callRun,results.symm,states.symm⟩

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.call_trace
