import InitECandidate.Solver.Input.HeaderGuards
import InitECandidate.Solver.Input.NonTimeoutSequenceCall

namespace InitECandidate.Solver.Input.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- An actual non-timeout run through a decoder guard either passes at no
source cost or funds and raises its real one-tick SszErr. The original tail
is retained only on the passing branch. -/
theorem guard_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (condition : ExpHOL 64)
    (error : BitVec 64) (active : Prop) [Decidable active] (continuation : ProgHOL 64)
    (test : eval source condition = some (.val (.word (if active then 1#64 else 0#64))))
    (code : source.code.lookup (ofString "ssz_fail") = some (SszFail.formals,SszFail.body,.one))
    (shape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.seq (.ite condition (.call (some (none,none)) (ofString "ssz_fail") [.const error]) .skip) continuation) = (result,post))
    (notTimeout : result ≠ some .timeOut) :
    (active ∧ 1 ≤ source.clock ∧ result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ post = emptyLocalsHOLFinite {source with clock := source.clock - 1}) ∨
    (¬ active ∧ evaluateHOLFiniteState source continuation = (result,post)) := by
  classical
  by_cases rejected : active
  · simp only [if_pos rejected,eval] at test
    have choice : evaluateHOLFiniteState source (.ite condition (.call (some (none,none)) (ofString "ssz_fail") [.const error]) .skip) =
        evaluateHOLFiniteState source (.call (some (none,none)) (ofString "ssz_fail") [.const error]) := by
      rw [evaluateHOLFiniteState_ite,test]
      simp
    have callRun : evaluateHOLFiniteState source (.seq (.call (some (none,none)) (ofString "ssz_fail") [.const error]) continuation) = (result,post) := by
      simpa only [evaluateHOLFiniteState_seq_line780,choice] using run
    obtain ⟨callee,called,_⟩ := SszFail.environment source.code.lookup error code
    have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [.const error] = some (SszFail.values error) := rfl
    obtain ⟨funded,_⟩ := sequence_call_non_timeout source post (some (none,none)) (ofString "ssz_fail") [.const error] (SszFail.values error) SszFail.body continuation callee .one args called result callRun notTimeout
    have failed := SszFail.call_execute source error code shape funded
    rw [evaluateHOLFiniteState_seq_line780,failed] at callRun
    exact Or.inl ⟨rejected,funded,(congrArg Prod.fst callRun).symm,(congrArg Prod.snd callRun).symm⟩
  · simp only [if_neg rejected,eval] at test
    have choice : evaluateHOLFiniteState source (.ite condition (.call (some (none,none)) (ofString "ssz_fail") [.const error]) .skip) = (none,source) := by
      rw [evaluateHOLFiniteState_ite,test]
      simp
    rw [evaluateHOLFiniteState_seq_line780,choice] at run
    exact Or.inr ⟨rejected,run⟩

end InitECandidate.Solver.Input.Header

#print axioms InitECandidate.Solver.Input.Header.guard_trace
