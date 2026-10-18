import InitECandidate.Solver.GasBudget.StackPopPrefixEffect

namespace InitECandidate.Solver.GasBudget.StackPop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- Actual exceptions through a literal pop chain: either the real stack
empties and throws before charge, at exactly initialDepth+1 caller clocks,
or all real pops complete and the real continuation throws. Every paid
prefix retains the full sp-only frame and physical regular ledger. -/
theorem pops_exception (names : List String) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp : BitVec 64)
    (continuation : ProgHOL 64)
    (code : source.code.lookup (ofString "stack_pop") = some ([], body, shape))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : source.memaddrs (frame + 16#64)) (cell : source.memory (frame + 16#64) = .word sp)
    (exceptionShape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (pops names continuation) = (some (.exception identifier payload), post)) :
    (identifier = ofString "EvmErr" ∧ payload = .val (.word 2#64) ∧ sp.toNat + 1 ≤ names.length ∧
      PrefixEffect source post frame (sp.toNat + 1) ∧ post.memory (frame + 16#64) = .word 0#64) ∨
    ∃ ready inner remaining,
      PrefixEffect source ready frame names.length ∧ ready.memory (frame + 16#64) = .word remaining ∧
      remaining.toNat + names.length = sp.toNat ∧
      evaluateHOLFiniteState ready continuation = (some (.exception identifier payload), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  induction names generalizing source post sp with
  | nil =>
    exact Or.inr ⟨source, post, sp, PrefixEffect.refl source frame, cell, by simp, run, rfl⟩
  | cons name names ih =>
    obtain ⟨positive, failed | returned⟩ := call_exception source post frame sp name (pops names continuation) code ev mapped cell exceptionShape identifier payload run
    · obtain ⟨zero, actualId, actualPayload, fields, clock⟩ := failed
      have effect := PrefixEffect.unchanged source post frame 1 positive clock fields
      have memory := congrArg PanSemStateFiniteExact.memory fields
      change post.memory = source.memory at memory
      have count : sp.toNat + 1 = 1 := by simp [zero]
      refine Or.inl ⟨actualId, actualPayload, ?_, ?_, ?_⟩
      · rw [count]
        simp only [List.length_cons]
        omega
      · rw [count]
        exact effect
      · rw [memory, cell, zero]
    · obtain ⟨nonzero, returned, firstPost, checked, continuationRun, postEq, budget, used⟩ := returned
      let first := resumed source frame sp name returned
      have firstCell : first.memory (frame + 16#64) = .word (sp - 1#64) := by
        change StoreWord.put source.memory (frame + 16#64) (sp - 1#64) (frame + 16#64) = _
        exact if_pos rfl
      have firstEffect := PrefixEffect.resumed source frame sp name returned positive
      have positiveWord : (1#64 : BitVec 64) ≤ sp := by
        change 1 ≤ sp.toNat
        by_contra small
        apply nonzero
        apply BitVec.eq_of_toNat_eq
        change sp.toNat = 0
        omega
      have stepDepth : (sp - 1#64).toNat + 1 = sp.toNat := by
        rw [BitVec.toNat_sub_of_le positiveWord]
        change sp.toNat - 1 + 1 = sp.toNat
        have positiveNat : 1 ≤ sp.toNat := positiveWord
        omega
      rcases ih first firstPost (sp - 1#64) code ev mapped firstCell exceptionShape continuationRun with failed | completed
      · obtain ⟨actualId, actualPayload, fitsNames, effect, zeroCell⟩ := failed
        have combined := firstEffect.trans effect
        have restored := combined.restore source name
        have paid : 1 + ((sp - 1#64).toNat + 1) = sp.toNat + 1 := by omega
        rw [paid] at restored
        refine Or.inl ⟨actualId, actualPayload, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · rw [postEq]
          exact restored
        · rw [postEq]
          exact zeroCell
      · obtain ⟨ready, inner, remaining, effect, readyCell, depth, restRun, scopeEq⟩ := completed
        have combined := firstEffect.trans effect
        have paid : 1 + names.length = (name :: names).length := by simp [Nat.add_comm]
        rw [paid] at combined
        refine Or.inr ⟨ready, inner, remaining, combined, readyCell, ?_, restRun, ?_⟩
        · simp only [List.length_cons]
          omega
        · rw [postEq]
          exact scopeEq

end InitECandidate.Solver.GasBudget.StackPop

#print axioms InitECandidate.Solver.GasBudget.StackPop.pops_exception
