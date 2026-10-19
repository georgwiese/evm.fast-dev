import InitECandidate.Solver.Mpt.AccountIsEmptyExecution
import InitECandidate.Solver.ClockPadding

namespace InitECandidate.Solver.Mpt.AccountIsEmpty
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (account emptyHash : BitVec 64)
    (image : AccountDecode.Image source account)
    (aLocal : source.locals.lookup (ofString "a") = some (.val (.word account)))
    (emptyGlobal : source.globals.lookup (ofString "empty_code_hash") = some (.val (.word emptyHash)))
    (emptyArena : AllocatedBytes.Arena emptyHash 32) (installed : Input.OriginalCode.Installed source.code) :
    source.clock - (evaluateHOLFiniteState source body).2.clock ≤ 6 := by
  by_cases enough : 6 ≤ source.clock
  · obtain ⟨paid,answer,post,bound,funded,binary,run,frame⟩ := execute source account emptyHash image aLocal emptyGlobal emptyArena installed enough
    have clock := congrArg PanSemStateFiniteExact.clock frame
    change post.clock = source.clock - paid at clock
    rw [run]
    change source.clock - post.clock ≤ _
    omega
  · omega

theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (account emptyHash : BitVec 64)
    (image : AccountDecode.Image source account)
    (aLocal : source.locals.lookup (ofString "a") = some (.val (.word account)))
    (emptyGlobal : source.globals.lookup (ofString "empty_code_hash") = some (.val (.word emptyHash)))
    (emptyArena : AllocatedBytes.Arena emptyHash 32) (installed : Input.OriginalCode.Installed source.code)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned),target)) :
    ∃ (paid : Nat) (answer : BitVec 64), paid ≤ 6 ∧ paid ≤ source.clock ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      returned = .val (.word answer) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - paid} := by
  let padded := {source with clock := source.clock + 6}
  let paddedImage := image.of_agreement source padded account rfl rfl rfl
  obtain ⟨paid,answer,post,bound,funded,binary,actual,modelFrame⟩ := execute padded account emptyHash paddedImage aLocal emptyGlobal emptyArena installed (by change 6 ≤ source.clock + 6; omega)
  have lifted := panPropsEvaluateAddClockEq body source (some (.returned returned)) target 6
    ⟨normal,by intro impossible; cases impossible⟩
  have resultEq := congrArg Prod.fst (lifted.symm.trans actual)
  have postEq := congrArg Prod.snd (lifted.symm.trans actual)
  change {target with clock := target.clock + 6} = post at postEq
  have frame : emptyLocalsHOLFinite {target with clock := target.clock + 6} =
      emptyLocalsHOLFinite {source with clock := source.clock + 6 - paid} := by
    rw [postEq]
    exact modelFrame
  have stripped := InitECandidate.Solver.strip_clock_padding source target source paid 6 (by omega) frame
  exact ⟨paid,answer,bound,stripped.1,binary,by simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using resultEq,stripped.2⟩

end InitECandidate.Solver.Mpt.AccountIsEmpty

#print axioms InitECandidate.Solver.Mpt.AccountIsEmpty.body_cost
#print axioms InitECandidate.Solver.Mpt.AccountIsEmpty.body_normal
