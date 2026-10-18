import InitECandidate.Solver.GasBudget.ForwardPrefix
import InitECandidate.Solver.GasBudget.RegularChargeMemory
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.GasBudget.ForwardPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- Actual normal execution through the original CALL-family forward-gas
subtree derives its one paid clock, exact used-counter debit, child seed,
remaining continuation and complete outside-word frame. The current used
word must fund the stipend; individual used words need not be monotone. -/
theorem normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame left used requested : BitVec 64) (words : U256Zero.Quad)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mcg : source.locals.lookup (ofString "mcg") = some (CallGas.pair (CallGas.capped requested left)
      (CallGas.capped requested left + CallGas.stipend words)))
    (gasCell : source.memory (frame + 64#64) = .word left) (usedCell : source.memory (frame + 184#64) = .word used)
    (code : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one))
    (cap : regularBudget source.memory frame ≤ 16777216) (funded : CallGas.stipend words ≤ used)
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (program continuation) = (some (.returned value), post)) :
    ∃ ready, 1 ≤ source.clock ∧ ready = {source with memory := ready.memory, clock := source.clock - 1} ∧
      evaluateHOLFiniteState ready continuation = (some (.returned value), post) ∧
      regularBudget ready.memory frame + (CallGas.capped requested left + CallGas.stipend words).toNat = regularBudget source.memory frame ∧
      ready.memory (frame + 184#64) = .word (used - CallGas.stipend words) ∧
      ready.memory (frame + 64#64) = .word (left - CallGas.capped requested left) ∧
      (wordAt ready.memory (frame + 184#64)).toNat + (CallGas.stipend words).toNat = used.toNat ∧
      (∀ address, address ≠ frame + 64#64 → address ≠ frame + 184#64 → ready.memory address = source.memory address) := by
  classical
  let debit := CallGas.capped requested left
  let forwarded := debit + CallGas.stipend words
  have debitRead : eval source debitExpression = some (.val (.word debit)) := by
    simp [eval, debitExpression, evalHOLExact, toExact, localVar, mcg, CallGas.pair, debit]
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [debitExpression] = some [.val (.word debit)] := by
    simp only [eval] at debitRead
    simp only [evalListHOLFinite, evalListHOLExact, debitRead]
  rw [program] at run
  have safe : Input.LocalPrefix (ofString "setup") (.call (some (none, none)) (ofString "charge_gas") [debitExpression]) :=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨charged, chargeRun, restRun, saved⟩ := safe.normal_continue source post _ value run
  obtain ⟨actualGas, actualUsed, positive, chargeClock, gasMapped, usedMapped, realGasCell, realUsedCell, affordable, chargeFrame, chargeBudget, chargedDebit, chargedCredit⟩ :=
    RegularCharge.call_normal source charged frame debit [debitExpression] args code ev cap chargeRun
  obtain ⟨memoryGas, memoryUsed, memoryGasCell, memoryUsedCell, memoryEq⟩ :=
    RegularCharge.call_memory source charged frame debit [debitExpression] args code ev cap chargeRun
  have gasEq : memoryGas = left := HolWordLab.word.inj (memoryGasCell.symm.trans gasCell)
  have usedEq : memoryUsed = used := HolWordLab.word.inj (memoryUsedCell.symm.trans usedCell)
  rw [gasEq, usedEq] at memoryEq
  have mcgC : charged.locals.lookup (ofString "mcg") = some (CallGas.pair debit forwarded) := by rw [chargeFrame]; exact mcg
  have evC : charged.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [chargeFrame]; exact ev
  have mappedC : charged.memaddrs (frame + 184#64) := by rw [chargeFrame]; exact usedMapped
  have storedUsed : charged.memory (frame + 184#64) = .word (used + debit) := by
    rw [memoryEq]
    exact WordWrites.write_unique source.memory (RegularCharge.writes frame left used debit) (frame + 184#64, used + debit)
      (by simp [RegularCharge.writes, offsets_ne frame 64#64 184#64 (by decide)]) (by simp [RegularCharge.writes])
  have forwardedRead : eval charged forwardedExpression = some (.val (.word forwarded)) := by
    simp [eval, forwardedExpression, evalHOLExact, toExact, localVar, mcgC, CallGas.pair]
  have usedRead := frame_read charged frame 184#64 (used + debit) evC mappedC storedUsed
  have counterRead : eval charged counterExpression = some (.val (.word ((used + debit) - forwarded))) := by
    simp only [eval] at usedRead forwardedRead ⊢
    simp only [counterExpression, evalHOLExact, evalListHOLExact, usedRead, forwardedRead]
    simp [valueIsWord, valueWord, wordOpHOL, wordOp]
  have storeRun := StoreWord.execute charged (frameAddress 184#64) counterExpression (frame + 184#64) ((used + debit) - forwarded)
    (address_read charged frame 184#64 evC) counterRead mappedC
  let ready := {charged with memory := StoreWord.put charged.memory (frame + 184#64) ((used + debit) - forwarded)}
  rw [evaluateHOLFiniteState_seq_line780, storeRun] at restRun
  have naturalCap := cap
  simp only [regularBudget, wordAt, gasCell, usedCell, MemoryBytes.wordBits] at naturalCap
  have leftFits : left.toNat + 2300 < 2^64 := by omega
  have budgetFits : left.toNat + used.toNat < 2^64 := by omega
  have fundedNat : (CallGas.stipend words).toNat ≤ used.toNat := funded
  have counter := (forward_counter_number words requested left used leftFits budgetFits fundedNat).1
  have exactUsed : (used + debit) - forwarded = used - CallGas.stipend words := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le funded]
    exact counter
  have usedReady : ready.memory (frame + 184#64) = .word (used - CallGas.stipend words) := by
    change StoreWord.put charged.memory (frame + 184#64) ((used + debit) - forwarded) (frame + 184#64) = _
    rw [StoreWord.put, if_pos rfl, exactUsed]
  have gasAway := offsets_ne frame 64#64 184#64 (by decide)
  have gasReady : ready.memory (frame + 64#64) = .word (left - debit) := by
    change StoreWord.put charged.memory (frame + 184#64) ((used + debit) - forwarded) (frame + 64#64) = _
    rw [StoreWord.put, if_neg gasAway, memoryEq]
    exact WordWrites.write_unique source.memory (RegularCharge.writes frame left used debit) (frame + 64#64, left - debit)
      (by simp [RegularCharge.writes, offsets_ne frame 64#64 184#64 (by decide)]) (by simp [RegularCharge.writes])
  have forwardAffordable : forwarded ≤ used + debit := by
    have seed := (CallGas.forwarded_number words requested left leftFits).2
    have debitBound : debit.toNat ≤ left.toNat := (CallGas.capped_number requested left).2
    have usedSum : (used + debit).toNat = used.toNat + debit.toNat := BitVec.toNat_add_of_lt (by change _ < 2^64; omega)
    change forwarded.toNat ≤ (used + debit).toNat
    change forwarded.toNat = debit.toNat + (CallGas.stipend words).toNat at seed
    rw [usedSum, seed]
    omega
  have ledger := used_debit_budget charged.memory frame (used + debit) forwarded storedUsed forwardAffordable
  refine ⟨ready, positive, ?_, restRun, ledger.trans chargeBudget, usedReady, gasReady, ?_, ?_⟩
  · dsimp only [ready]
    rw [chargeFrame]
  · simp only [wordAt, usedReady, MemoryBytes.wordBits, BitVec.toNat_sub_of_le funded]
    omega
  · intro address notGas notUsed
    change StoreWord.put charged.memory (frame + 184#64) ((used + debit) - forwarded) address = source.memory address
    rw [StoreWord.put, if_neg notUsed]
    exact RegularCharge.call_other_word source charged frame debit address [debitExpression] args code ev cap chargeRun notGas notUsed

end InitECandidate.Solver.GasBudget.ForwardPrefix

#print axioms InitECandidate.Solver.GasBudget.ForwardPrefix.normal
