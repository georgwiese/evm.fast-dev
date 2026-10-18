import InitECandidate.Solver.GasBudget.StackPopsException
import InitECandidate.Solver.GasBudget.RegularChargeLiteralOutcomes
import InitECandidate.Solver.GasBudget.OpcodeChargePrefix

namespace InitECandidate.Solver.GasBudget.OpcodeChargePrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual effects at the first charge, before the remaining opcode body. -/
structure ChargedEffect (source ready : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp remaining : BitVec 64) (popCount : Nat) (amount : BitVec 64) : Prop where
  fits : popCount + 1 ≤ source.clock
  clock : ready.clock = source.clock - (popCount + 1)
  fields : emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := ready.clock}
  budget : regularBudget ready.memory frame = regularBudget source.memory frame
  used : (wordAt ready.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + amount.toNat
  spCell : ready.memory (frame + 16#64) = .word remaining
  depth : remaining.toNat + popCount = sp.toNat
  outside : ∀ address, address ≠ frame + 16#64 → address ≠ frame + 64#64 → address ≠ frame + 184#64 →
    ready.memory address = source.memory address

/-- A real opcode-prefix exception is either underflow before charge,
insufficient gas before mutation, or an exception from the real suffix after
an affordable charge. All prefix clocks, physical effects and credit are
derived; no helper/continuation execution or future funding is supplied. -/
theorem exception (names : List String) (amount : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp gas used : BitVec 64)
    (continuation : ProgHOL 64)
    (stackCode : source.code.lookup (ofString "stack_pop") = some ([], StackPop.body, StackPop.shape))
    (chargeCode : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (exceptionShape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (program names amount continuation) = (some (.exception identifier payload), post)) :
    (identifier = ofString "EvmErr" ∧ payload = .val (.word 2#64) ∧ sp.toNat + 1 ≤ names.length ∧
      StackPop.PrefixEffect source post frame (sp.toNat + 1) ∧ post.memory (frame + 16#64) = .word 0#64) ∨
    (identifier = ofString "EvmErr" ∧ payload = .val (.word 4#64) ∧ names.length ≤ sp.toNat ∧ gas < amount ∧
      StackPop.PrefixEffect source post frame (names.length + 1)) ∨
    ∃ ready inner remaining,
      ChargedEffect source ready frame sp remaining names.length amount ∧
      evaluateHOLFiniteState ready continuation = (some (.exception identifier payload), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  rcases StackPop.pops_exception names source post frame sp _ stackCode ev spMapped spCell exceptionShape identifier payload run with underflow | popped
  · exact Or.inl underflow
  · obtain ⟨popped, scopePost, remaining, popEffect, poppedSP, depth, remainingRun, scopeEq⟩ := popped
    have globals := congrArg PanSemStateFiniteExact.globals popEffect.fields
    change popped.globals = source.globals at globals
    have code := congrArg PanSemStateFiniteExact.code popEffect.fields
    change popped.code = source.code at code
    have domain := congrArg PanSemStateFiniteExact.memaddrs popEffect.fields
    change popped.memaddrs = source.memaddrs at domain
    have shapes := congrArg PanSemStateFiniteExact.eshapes popEffect.fields
    change popped.eshapes = source.eshapes at shapes
    have poppedEV : popped.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [globals]; exact ev
    have poppedCode : popped.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one) := by rw [code]; exact chargeCode
    have poppedGasMapped : popped.memaddrs (frame + 64#64) := by rw [domain]; exact gasMapped
    have poppedUsedMapped : popped.memaddrs (frame + 184#64) := by rw [domain]; exact usedMapped
    have poppedGasCell : popped.memory (frame + 64#64) = .word gas :=
      (popEffect.outside _ (offsets_ne frame 64#64 16#64 (by decide))).trans gasCell
    have poppedUsedCell : popped.memory (frame + 184#64) = .word used := popEffect.used.trans usedCell
    have poppedCap : regularBudget popped.memory frame ≤ 16777216 := by rw [popEffect.budget]; exact cap
    have poppedShape : popped.eshapes.lookup (ofString "EvmErr") = some .one := by rw [shapes]; exact exceptionShape
    obtain ⟨charged, chargeRun, chargeClock, chargeFrame, chargeMemory, chargeBudget, credit, outside⟩ :=
      RegularCharge.literal_outcomes popped frame gas used amount poppedCode poppedEV poppedGasMapped poppedUsedMapped poppedGasCell poppedUsedCell poppedCap poppedShape
    rw [evaluateHOLFiniteState_seq_line780, chargeRun] at remainingRun
    by_cases zero : popped.clock = 0
    · simp only [RegularCharge.literalResult, if_pos zero] at remainingRun
      cases remainingRun
    · have positive : 1 ≤ popped.clock := by omega
      by_cases affordable : amount ≤ gas
      · simp only [RegularCharge.literalResult, if_neg zero, if_pos affordable] at remainingRun
        have fits : names.length + 1 ≤ source.clock := by
          have prior := popEffect.fits
          have clock := popEffect.clock
          omega
        have clock : charged.clock = source.clock - (names.length + 1) := by rw [chargeClock, popEffect.clock]; omega
        have fields : emptyLocalsHOLFinite charged = emptyLocalsHOLFinite {popped with memory := charged.memory, clock := charged.clock} := by
          rw [chargeClock]
          exact chargeFrame
        have lifted := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
          emptyLocalsHOLFinite {state with memory := charged.memory, clock := charged.clock}) popEffect.fields
        have chargedSP : charged.memory (frame + 16#64) = .word remaining :=
          (outside _ (offsets_ne frame 16#64 64#64 (by decide)) (offsets_ne frame 16#64 184#64 (by decide))).trans poppedSP
        have usedCredit : (wordAt charged.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + amount.toNat := by
          simp only [RegularCharge.literalDebit, if_neg zero, RegularCharge.debit, if_pos affordable] at credit
          simpa only [wordAt, usedCell, WitnessRadix.MemoryBytes.wordBits] using credit
        refine Or.inr (Or.inr ⟨charged, scopePost, remaining, ⟨fits, clock, fields.trans lifted, chargeBudget.trans popEffect.budget,
          usedCredit, chargedSP, depth, ?_⟩, remainingRun, scopeEq⟩)
        intro address notSP notGas notUsed
        exact (outside address notGas notUsed).trans (popEffect.outside address notSP)
      · simp only [RegularCharge.literalResult, if_neg zero, if_neg affordable] at remainingRun
        have ids : identifier = ofString "EvmErr" ∧ payload = .val (.word 4#64) := by
          simpa only [Option.some.injEq, PanSemResultExact.exception.injEq] using (congrArg Prod.fst remainingRun).symm
        have same := congrArg Prod.snd remainingRun
        change charged = scopePost at same
        have postFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite charged := scopeEq.trans (congrArg emptyLocalsHOLFinite same.symm)
        simp only [if_neg zero, RegularCharge.memoryAfter, if_neg affordable] at chargeMemory
        rw [chargeMemory] at chargeFrame
        have effect := StackPop.PrefixEffect.unchanged popped charged frame 1 positive chargeClock chargeFrame
        have total := (popEffect.trans effect).of_emptyLocals postFrame
        have unavailable : gas < amount := by change ¬amount.toNat ≤ gas.toNat at affordable; change gas.toNat < amount.toNat; omega
        exact Or.inr (Or.inl ⟨ids.1, ids.2, by omega, unavailable, total⟩)

end InitECandidate.Solver.GasBudget.OpcodeChargePrefix

#print axioms InitECandidate.Solver.GasBudget.OpcodeChargePrefix.exception
