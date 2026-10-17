import InitECandidate.Solver.Input.BytesList.Reads

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array maximum value : BitVec 64) (index count : Nat)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (r : source.locals.lookup (ofString "r")=some (pairValue array count))
    (m : source.locals.lookup (ofString "maxb")=some (.val (.word maximum)))
    (mapped : source.memaddrs (cell array index)) (stored : source.memory (cell array index)=.word value)
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source loopBody=
      if maximum.toNat<value.toNat then
        (some (.exception (ofString "SszErr") (.val (.word 70#64))),emptyLocalsHOLFinite {source with clock:=source.clock-1})
      else (none,bind source "i" (BitVec.ofNat 64 (index+1))) := by
  have test:=length_test source array maximum value index count i r m mapped stored
  have guard:=Header.test_guard_execute source lengthTest 70#64 (maximum.toNat<value.toNat) test failCode exceptionShape enough
  change evaluateHOLFiniteState source lengthGuard=_ at guard
  by_cases rejected : maximum.toNat<value.toNat
  · simp only [if_pos rejected] at guard ⊢
    exact WitnessRadix.StateSteps.stopped_sequence source _ lengthGuard increment (.exception (ofString "SszErr") (.val (.word 70#64))) guard
      (by change source.clock-1≤source.clock; omega)
  · simp only [if_neg rejected] at guard ⊢
    have incrementRead : eval source (.op .add [localVar "i",.const 1#64])=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
      simpa only [Scalar.plus,BitVec.ofNat_add] using Scalar.plus_read source (localVar "i") (BitVec.ofNat 64 index) 1 (Request.local_word source "i" _ i)
    have assign:=WitnessRadix.StateSteps.assign_execute source "i" (.op .add [localVar "i",.const 1#64]) _ _ i incrementRead
    exact (WitnessRadix.StateSteps.next_sequence source source lengthGuard increment guard (Nat.le_refl _)).trans assign

end InitECandidate.Solver.Input.BytesList

#print axioms InitECandidate.Solver.Input.BytesList.body_execute
