import InitECandidate.Solver.Input.RequestSetup

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

theorem length_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) (small : length<2^64)
    (localPresent : source.locals.lookup (ofString "nlen")=some (.val (.word (BitVec.ofNat 64 length)))) :
    eval source lengthTest=some (.val (.word (if length<44 then 1#64 else 0#64))) := by
  classical
  have encoded : (BitVec.ofNat 64 length).toNat=length := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  simp [eval,lengthTest,localVar,evalHOLExact,toExact,localPresent,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,encoded]

/-- All real prefix scopes and the actual request-length guard. Rejection
cannot resume the request decoder; passing exposes its actual live locals. -/
theorem prefix_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor : BitVec 64) (witness : Nat) (witnessSmall : witness<2^64)
    (restoreStack : PanSemStateFiniteExact 64 Guest.HostMemory→PanSemStateFiniteExact 64 Guest.HostMemory)
    (setup : Executes source actions (prepared source input pointer cursor witness) restoreStack)
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 2≤source.clock) :
    evaluateHOLFiniteState source prefixBody=
      if witness-16<44 then
        (some (.exception (ofString "SszErr") (.val (.word 81#64))),
          restoreStack (emptyLocalsHOLFinite {prepared source input pointer cursor witness with clock:=(prepared source input pointer cursor witness).clock-1}))
      else (let output:=evaluateHOLFiniteState (prepared source input pointer cursor witness) requestBody;
        (output.1,restoreStack output.2)) := by
  classical
  let ready:=prepared source input pointer cursor witness
  have test:=length_test_read ready (witness-16) (by omega) (bind_lookup_same _ _ _)
  have guarded : evaluateHOLFiniteState ready lengthGuard=
      if witness-16<44 then
        (some (.exception (ofString "SszErr") (.val (.word 81#64))),emptyLocalsHOLFinite {ready with clock:=ready.clock-1})
      else (none,ready) :=
    Header.test_guard_execute ready lengthTest 81#64 (witness-16<44) test failCode exceptionShape (by change 1≤source.clock-1; omega)
  rw [actions_shape,WitnessRadix.ProgramPrefix.execute setup]
  by_cases bad : witness-16<44
  · simp only [if_pos bad] at guarded ⊢
    rw [WitnessRadix.StateSteps.stopped_sequence ready _ _ _ _ guarded (by change source.clock-1-1≤source.clock-1; omega)]
  · simp only [if_neg bad] at guarded ⊢
    rw [WitnessRadix.StateSteps.next_sequence ready ready _ _ guarded (Nat.le_refl _)]

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.length_test_read
#print axioms InitECandidate.Solver.Input.Request.prefix_execute
