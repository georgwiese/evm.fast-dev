import InitECandidate.Solver.GasBudget.CopyCostProgram

namespace InitECandidate.Solver.GasBudget.CopyCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem fee_read (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (cell : source.locals.lookup (ofString "w") = some (.val (.word word))) :
    eval source kind.fee = some (.val (.word (BitVec.ofNat 64 kind.base + BitVec.ofNat 64 kind.slope * word))) := by
  simp [Kind.fee, eval, evalHOLExact, evalListHOLExact, toExact, localVar, cell, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]

theorem setup_normal (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source kind.program = (some (.returned value), post)) :
    ∃ (paid : Nat) (amount : BitVec 64) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ 26 ∧ kind.base ≤ amount.toNat ∧ StackPop.PrefixEffect source ready frame paid ∧
      evaluateHOLFiniteState ready (OpcodeChargePrefix.program [] amount kind.suffix) = (some (.returned value), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  rw [Kind.program] at normal
  obtain ⟨paidN, n, nPost, nonzeroN, boundN, fitsN, wordsRun, nEq⟩ :=
    Input.PricedReadOnlyPrefix.normal source post "n" .one (ofString "sat_word") [localVar "size"] kind.afterSat
      ArithmeticEffects.Kind.sat_word.signature.1 ArithmeticEffects.Kind.sat_word.body ArithmeticEffects.Kind.sat_word.signature.2.2 0
      (OriginalCodeEnvironment.arithmetic source.code installed .sat_word)
      (ArithmeticEffects.pure_sat_word source.code (OriginalCodeEnvironment.arithmetic source.code installed))
      (ArithmeticEffects.price_sat_word source.code (OriginalCodeEnvironment.arithmetic source.code installed)) value normal
  let first := setVarHOLFinite (ofString "n") n {source with clock := source.clock - paidN}
  have firstEffect : StackPop.PrefixEffect source first frame paidN := StackPop.PrefixEffect.unchanged source first frame paidN fitsN rfl rfl
  obtain ⟨word, paidW, wPost, small, nonzeroW, boundW, fitsW, memoryRun, wEq⟩ :=
    WordsOf.normal_prefix first nPost "w" [localVar "n"] kind.afterWords installed value wordsRun
  let second := bind {first with clock := first.clock - paidW} "w" word
  have secondEffect : StackPop.PrefixEffect first second frame paidW := StackPop.PrefixEffect.unchanged first second frame paidW fitsW rfl rfl
  obtain ⟨paidX, x, xPost, nonzeroX, boundX, fitsX, feeRun, xEq⟩ :=
    Input.PricedReadOnlyPrefix.normal second wPost "x" ChargeWithMemory.pair (ofString "extend_memory_cost1")
      [localVar kind.start, localVar "size"] kind.afterCost MemoryCostEffects.Kind.extend_memory_cost1.signature.1
      MemoryCostEffects.Kind.extend_memory_cost1.body MemoryCostEffects.Kind.extend_memory_cost1.signature.2.2 20
      (MemoryCostEffects.entry second.code installed .extend_memory_cost1)
      (MemoryCostEffects.pure_extend_memory_cost1 second.code installed)
      (MemoryCostEffects.price_extend_memory_cost1 second.code installed) value memoryRun
  let third := setVarHOLFinite (ofString "x") x {second with clock := second.clock - paidX}
  have thirdEffect : StackPop.PrefixEffect second third frame paidX := StackPop.PrefixEffect.unchanged second third frame paidX fitsX rfl rfl
  have wordCell : third.locals.lookup (ofString "w") = some (.val (.word word)) := by
    simpa [third, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show (ofString "x" == ofString "w") = false from by decide] using
      (show second.locals.lookup (ofString "w") = some (.val (.word word)) from bind_lookup_same _ _ _)
  have addCode := OriginalCodeEnvironment.arithmetic third.code installed .add_sat
  rw [ChargeWithMemory.add_signature] at addCode
  obtain ⟨a, b, inner, funded, arguments, lower, chargeRun, costEq⟩ :=
    SaturatingAdd.normal_prefix third xPost "cost" [kind.fee, .rfield 0 (localVar "x")] kind.afterFee addCode value feeRun
  have actualFee : a = BitVec.ofNat 64 kind.base + BitVec.ofNat 64 kind.slope * word :=
    Input.ArgumentValues.first_of_pair third kind.fee (.rfield 0 (localVar "x")) _ a b (fee_read kind third word wordCell) arguments
  have feeBound := (WordsOf.fee_numbers word small kind.base kind.slope (by cases kind <;> decide) (by cases kind <;> decide)).2
  let ready := bind {third with clock := third.clock - 1} "cost" (SaturatingAdd.resultWord a b)
  have lastEffect : StackPop.PrefixEffect third ready frame 1 := StackPop.PrefixEffect.unchanged third ready frame 1 funded rfl rfl
  have costCell : ready.locals.lookup (ofString "cost") = some (.val (.word (SaturatingAdd.resultWord a b))) := bind_lookup_same _ _ _
  rw [charge_choice kind ready _ costCell] at chargeRun
  refine ⟨paidN + paidW + paidX + 1, SaturatingAdd.resultWord a b, ready, inner, by omega, ?_,
    ((firstEffect.trans secondEffect).trans thirdEffect).trans lastEffect, chargeRun, ?_⟩
  · rw [← actualFee] at feeBound
    exact feeBound.trans lower
  · rw [nEq, wEq, xEq, costEq]
    rfl

end InitECandidate.Solver.GasBudget.CopyCost

#print axioms InitECandidate.Solver.GasBudget.CopyCost.setup_normal
