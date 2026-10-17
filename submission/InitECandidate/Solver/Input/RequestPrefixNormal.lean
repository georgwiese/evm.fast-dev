import InitECandidate.Solver.Input.RequestPrefixEntry

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

/-- Actual normal request-prefix execution establishes a safe >=44-byte
request at blob+18 and at least62 encoded input bytes, without assuming them.
All real declaration restorations remain in the execution premise. -/
theorem normal_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor : BitVec 64) (witness : Nat) (upper : witness≤input.length%2^64-2)
    (restoreStack : PanSemStateFiniteExact 64 Guest.HostMemory→PanSemStateFiniteExact 64 Guest.HostMemory)
    (setup : Executes source actions (prepared source input pointer cursor witness) restoreStack)
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 2≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source prefixBody=(some (.returned value),post)) :
    62≤input.length%2^64 ∧ 44≤witness-16 ∧ witness-16≤input.length%2^64-18 ∧
      (prepared source input pointer cursor witness).locals.lookup (ofString "np")=some (.val (.word (pointer+18#64))) ∧
      (prepared source input pointer cursor witness).locals.lookup (ofString "nlen")=some (.val (.word (BitVec.ofNat 64 (witness-16)))) ∧
      ∃ innerPost,evaluateHOLFiniteState (prepared source input pointer cursor witness) requestBody=(some (.returned value),innerPost) := by
  classical
  have encodedSmall : input.length%2^64<2^64 := Nat.mod_lt _ (by decide)
  have witnessSmall : witness<2^64 := by omega
  rw [prefix_execute source input pointer cursor witness witnessSmall restoreStack setup failCode exceptionShape enough] at run
  by_cases bad : witness-16<44
  · simp only [if_pos bad] at run
    have impossible:=congrArg Prod.fst run
    cases impossible
  · simp only [if_neg bad] at run
    have resultEq:=congrArg Prod.fst run
    change (evaluateHOLFiniteState (prepared source input pointer cursor witness) requestBody).1=some (.returned value) at resultEq
    refine ⟨by omega,by omega,by omega,?_,bind_lookup_same _ _ _,(evaluateHOLFiniteState (prepared source input pointer cursor witness) requestBody).2,?_⟩
    · exact (bind_lookup_other (positioned source input pointer cursor witness) "nlen" "np" _ (by decide)).trans (bind_lookup_same _ _ _)
    · apply Prod.ext
      · exact resultEq
      · rfl

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.normal_prefix
