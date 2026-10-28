import InitECandidate.Solver.Headers.ValidateSyntax
import InitECandidate.Solver.Input.ClockCost
import InitECandidate.Solver.Input.SequenceChoice
import InitECandidate.Solver.Input.LiteralGuardNormal

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Original unsigned header-count guard: early failures spend no source
tick, and only actual counts at most256 reach the allocation scopes. -/
theorem count_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64)
    (cell : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) :
    source.clock-post.clock≤0 ∨ count.toNat≤256 ∧ evaluateHOLFiniteState source afterGuard=(result,post) := by
  have dispatch : evaluateHOLFiniteState source countGuard=
      if 256<count.toNat then evaluateHOLFiniteState source (.raise (ofString "BlockErr") (.const 1#64)) else (none,source) := by
    by_cases large : 256<count.toNat
    · simp [countGuard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,localVar,toExact,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,large,Nat.not_le.mpr large]
    · simp [countGuard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,localVar,toExact,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,large,Nat.le_of_not_gt large]
  have picked:=Input.sequence_choice source countGuard (.raise (ofString "BlockErr") (.const 1#64)) afterGuard (256<count.toNat) dispatch
    (fun current=>Input.raise_ne_none current (ofString "BlockErr") (.const 1#64))
  rw [shapes.1,picked] at run
  by_cases large : 256<count.toNat
  · rw [if_pos large] at run
    have price:=Input.ClockCost.raised source.code (ofString "BlockErr") (.const 1#64) source rfl
    rw [run] at price
    exact Or.inl price
  · rw [if_neg large] at run
    exact Or.inr ⟨by omega,run⟩

theorem count_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64)
    (cell : source.locals.lookup (ofString "n")=some (.val (.word count))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    count.toNat≤256 ∧ evaluateHOLFiniteState source afterGuard=(some (.returned value),post) := by
  have read : eval source (.cmp .lower (.const 256#64) (localVar "n"))=
      some (.val (.word (if 256<count.toNat then 1#64 else 0#64))) := by
    simp [eval,evalHOLExact,localVar,toExact,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  rw [shapes.1] at normal
  obtain ⟨passed,continued⟩ := Input.literal_guard_normal source post _ (ofString "BlockErr") 1#64 (256<count.toNat) read afterGuard value normal
  exact ⟨by omega,continued⟩

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.count_trace
#print axioms InitECandidate.Solver.Headers.CurrentValidate.count_returned
