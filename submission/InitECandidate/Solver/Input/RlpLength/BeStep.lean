import InitECandidate.Solver.Input.RlpLength.BeProgram

namespace InitECandidate.Solver.Input.RlpLength.Be
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (v : source.locals.lookup (ofString "v")=some (.val (.word value))) :
    eval source loopTest=some (.val (.word (if value=0#64 then 0#64 else 1#64))) := by
  classical
  simp [eval,loopTest,localVar,evalHOLExact,toExact,v,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64) (count : Nat)
    (v : source.locals.lookup (ofString "v")=some (.val (.word value)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))) :
    evaluateHOLFiniteState source loopBody=(none,step source value count) := by
  classical
  have readV : eval source shiftExpression=some (.val (.word (value>>>(8:Nat)))) := by
    simp [eval,shiftExpression,localVar,evalHOLExact,toExact,v,wordShiftHOL]
  have runV:=WitnessRadix.StateSteps.assign_execute source "v" shiftExpression value _ v readV
  let first:=bind source "v" (value>>>(8:Nat))
  have savedN : first.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))) :=
    (bind_lookup_other source "v" "n" _ (by decide)).trans n
  have readN : eval first incrementExpression=some (.val (.word (BitVec.ofNat 64 (count+1)))) := by
    simp [eval,incrementExpression,localVar,evalHOLExact,evalListHOLExact,toExact,savedN,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  have runN:=WitnessRadix.StateSteps.assign_execute first "n" incrementExpression _ _ savedN readN
  rw [loopBody,WitnessRadix.StateSteps.next_sequence source first _ _ runV (Nat.le_refl _)]
  exact runN

theorem step_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64) (count : Nat) :
    (step source value count).locals.lookup (ofString "v")=some (.val (.word (value>>>(8:Nat)))) ∧
    (step source value count).locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 (count+1)))) := by
  exact ⟨(bind_lookup_other _ "n" "v" _ (by decide)).trans (bind_lookup_same _ _ _),bind_lookup_same _ _ _⟩

theorem step_state (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64) (count : Nat) :
    step source value count={source with locals:=(step source value count).locals} := rfl

end InitECandidate.Solver.Input.RlpLength.Be

#print axioms InitECandidate.Solver.Input.RlpLength.Be.body_execute
#print axioms InitECandidate.Solver.Input.RlpLength.Be.step_fields
