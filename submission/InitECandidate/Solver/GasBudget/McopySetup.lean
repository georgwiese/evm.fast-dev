import InitECandidate.Solver.GasBudget.McopyProgram

namespace InitECandidate.Solver.GasBudget.Mcopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem setup_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current : BitVec 64)
    (view : MemoryExpansionCost.View source frame current) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source program = (some (.returned value), post)) :
    ∃ (paid : Nat) (amount : BitVec 64) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ 48 ∧ 3 ≤ amount.toNat ∧ StackPop.PrefixEffect source ready frame paid ∧
      evaluateHOLFiniteState ready (OpcodeChargePrefix.program [] amount suffix) = (some (.returned value), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  rw [program] at normal
  obtain ⟨paidN, n, nPost, nonzeroN, boundN, fitsN, wordsRun, nEq⟩ :=
    Input.PricedReadOnlyPrefix.normal source post "n" .one (ofString "sat_word") [localVar "len"] afterSat
      ArithmeticEffects.Kind.sat_word.signature.1 ArithmeticEffects.Kind.sat_word.body ArithmeticEffects.Kind.sat_word.signature.2.2 0
      (OriginalCodeEnvironment.arithmetic source.code view.installed .sat_word)
      (ArithmeticEffects.pure_sat_word source.code (OriginalCodeEnvironment.arithmetic source.code view.installed))
      (ArithmeticEffects.price_sat_word source.code (OriginalCodeEnvironment.arithmetic source.code view.installed)) value normal
  let first := setVarHOLFinite (ofString "n") n {source with clock := source.clock - paidN}
  have firstEffect : StackPop.PrefixEffect source first frame paidN := StackPop.PrefixEffect.unchanged source first frame paidN fitsN rfl rfl
  obtain ⟨word, paidW, wPost, small, nonzeroW, boundW, fitsW, memoryRun, wEq⟩ :=
    WordsOf.normal_prefix first nPost "w" [localVar "n"] afterWords view.installed value wordsRun
  let second := bind {first with clock := first.clock - paidW} "w" word
  have secondEffect : StackPop.PrefixEffect first second frame paidW := StackPop.PrefixEffect.unchanged first second frame paidW fitsW rfl rfl
  have secondView : MemoryExpansionCost.View second frame current := view.after_erase rfl
  obtain ⟨paidX, x, xPost, nonzeroX, boundX, fitsX, feeRun, xEq⟩ :=
    MemoryExpansionCost2.any_normal_prefix second wPost frame current secondView "x"
      [localVar "src", localVar "len", localVar "dst", localVar "len"] afterCost value memoryRun
  let third := setVarHOLFinite (ofString "x") x {second with clock := second.clock - paidX}
  have thirdEffect : StackPop.PrefixEffect second third frame paidX := StackPop.PrefixEffect.unchanged second third frame paidX fitsX rfl rfl
  have wordCell : third.locals.lookup (ofString "w") = some (.val (.word word)) := by
    simpa [third, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show (ofString "x" == ofString "w") = false from by decide] using
      (show second.locals.lookup (ofString "w") = some (.val (.word word)) from bind_lookup_same _ _ _)
  have addCode := OriginalCodeEnvironment.arithmetic third.code view.installed .add_sat
  rw [ChargeWithMemory.add_signature] at addCode
  obtain ⟨a, b, inner, funded, arguments, lower, chargeRun, costEq⟩ :=
    SaturatingAdd.normal_prefix third xPost "cost" [fee, .rfield 0 (localVar "x")] afterFee addCode value feeRun
  have actualFee : a = BitVec.ofNat 64 3 + BitVec.ofNat 64 3 * word :=
    Input.ArgumentValues.first_of_pair third fee (.rfield 0 (localVar "x")) _ a b (fee_read third word wordCell) arguments
  have feeBound := (WordsOf.fee_numbers word small 3 3 (by decide) (by decide)).2
  let ready := bind {third with clock := third.clock - 1} "cost" (SaturatingAdd.resultWord a b)
  have lastEffect : StackPop.PrefixEffect third ready frame 1 := StackPop.PrefixEffect.unchanged third ready frame 1 funded rfl rfl
  have costCell : ready.locals.lookup (ofString "cost") = some (.val (.word (SaturatingAdd.resultWord a b))) := bind_lookup_same _ _ _
  rw [charge_choice ready _ costCell] at chargeRun
  refine ⟨paidN + paidW + paidX + 1, SaturatingAdd.resultWord a b, ready, inner, by omega, ?_,
    ((firstEffect.trans secondEffect).trans thirdEffect).trans lastEffect, chargeRun, ?_⟩
  · rw [← actualFee] at feeBound
    exact feeBound.trans lower
  · rw [nEq, wEq, xEq, costEq]
    rfl

end InitECandidate.Solver.GasBudget.Mcopy

#print axioms InitECandidate.Solver.GasBudget.Mcopy.setup_normal
