import InitECandidate.Solver.Input.HeaderSchema

namespace InitECandidate.Solver.Input.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real conditional decoder-error call, including the actual exception and
one call clock on rejection; the passing path changes no state field. -/
theorem test_guard_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (condition : ExpHOL 64)
    (error : BitVec 64) (active : Prop) [Decidable active]
    (test : eval source condition=some (.val (.word (if active then 1#64 else 0#64))))
    (code : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (.ite condition (.call (some (none,none)) (ofString "ssz_fail") [.const error]) .skip)=
      if active then (some (.exception (ofString "SszErr") (.val (.word error))),emptyLocalsHOLFinite {source with clock:=source.clock-1})
      else (none,source) := by
  classical
  simp only [eval] at test
  by_cases rejected : active
  · simp only [if_pos rejected] at test ⊢
    rw [evaluateHOLFiniteState_ite,test]
    have failed:=SszFail.call_execute source error code exceptionShape enough
    simpa using failed
  · simp only [if_neg rejected] at test ⊢
    rw [evaluateHOLFiniteState_ite,test]
    simp

theorem length_guard_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length limit error : Nat)
    (lengthSmall : length<2^64) (limitSmall : limit<2^64)
    (localPresent : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (code : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (lengthGuard limit error)=
      if length<limit then (some (.exception (ofString "SszErr") (.val (.word (BitVec.ofNat 64 error)))),emptyLocalsHOLFinite {source with clock:=source.clock-1})
      else (none,source) :=
  test_guard_execute source (lengthTest limit) (BitVec.ofNat 64 error) (length<limit)
    (length_read source length limit lengthSmall limitSmall localPresent) code exceptionShape enough

theorem schema_guard_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64)
    (heap : Blob.HeapInput source input pointer) (inside : 2≤input.length%2^64)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (code : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source schemaGuard=
      if Guest.GasLimit.byte input 0≠21 ∨ Guest.GasLimit.byte input 1≠1 then
        (some (.exception (ofString "SszErr") (.val (.word 2#64))),emptyLocalsHOLFinite {source with clock:=source.clock-1})
      else (none,source) :=
  test_guard_execute source schemaTest 2#64 _ (schema_read source input pointer heap inside pointerLocal) code exceptionShape enough

end InitECandidate.Solver.Input.Header

#print axioms InitECandidate.Solver.Input.Header.test_guard_execute
#print axioms InitECandidate.Solver.Input.Header.length_guard_execute
#print axioms InitECandidate.Solver.Input.Header.schema_guard_execute
