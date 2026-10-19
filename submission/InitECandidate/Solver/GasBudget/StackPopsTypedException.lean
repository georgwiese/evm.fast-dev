import InitECandidate.Solver.GasBudget.StackPopsTyped
import InitECandidate.Solver.GasBudget.StackPopsException

namespace InitECandidate.Solver.GasBudget.StackPop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

private theorem resumed_other_exception (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp : BitVec 64)
    (name key : String) (value : ValueHOL 64) (different : ofString name ≠ ofString key) :
    (resumed source frame sp name value).locals.lookup (ofString key) = source.locals.lookup (ofString key) := by
  simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different, Ne.symm different]

/-- Every real exceptional pop chain either underflows at its actual empty
stack, or exposes all the genuine typed arguments and original continuation.
Caller locals outside the distinct declaration names survive the prefix. -/
theorem pops_typed_exception (names : List String) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp : BitVec 64)
    (distinct : (names.map ofString).Nodup) (continuation : ProgHOL 64)
    (code : source.code.lookup (ofString "stack_pop") = some ([], body, shape))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : source.memaddrs (frame + 16#64)) (cell : source.memory (frame + 16#64) = .word sp)
    (exceptionShape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (pops names continuation) = (some (.exception identifier payload), post)) :
    (identifier = ofString "EvmErr" ∧ payload = .val (.word 2#64) ∧ sp.toNat + 1 ≤ names.length ∧
      PrefixEffect source post frame (sp.toNat + 1) ∧ post.memory (frame + 16#64) = .word 0#64) ∨
    ∃ ready inner remaining, PrefixEffect source ready frame names.length ∧ ready.memory (frame + 16#64) = .word remaining ∧
      remaining.toNat + names.length = sp.toNat ∧
      (∀ name ∈ names, ∃ words : U256Value.Words, ready.locals.lookup (ofString name) = some (U256Value.tuple words)) ∧
      (∀ key : String, (∀ name ∈ names, ofString name ≠ ofString key) → ready.locals.lookup (ofString key) = source.locals.lookup (ofString key)) ∧
      evaluateHOLFiniteState ready continuation = (some (.exception identifier payload), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  induction names generalizing source post sp with
  | nil => exact Or.inr ⟨source, post, sp, PrefixEffect.refl source frame, cell, by simp, by simp, by intro key away; rfl, run, rfl⟩
  | cons name names ih =>
    have nodup := List.nodup_cons.mp distinct
    obtain ⟨positive, failed | returned⟩ := call_exception source post frame sp name (pops names continuation) code ev mapped cell exceptionShape identifier payload run
    · obtain ⟨zero, actualId, actualPayload, fields, clock⟩ := failed
      have effect := PrefixEffect.unchanged source post frame 1 positive clock fields
      have memory := congrArg PanSemStateFiniteExact.memory fields
      change post.memory = source.memory at memory
      have count : sp.toNat + 1 = 1 := by simp [zero]
      refine Or.inl ⟨actualId, actualPayload, ?_, ?_, ?_⟩
      · rw [count]; simp only [List.length_cons]; omega
      · rw [count]; exact effect
      · rw [memory, cell, zero]
    · obtain ⟨nonzero, returned, firstPost, checked, continuationRun, scope, budget, used⟩ := returned
      obtain ⟨words, resultEq⟩ := U256Value.of_shape returned ((shapeEqHOL_eq_true _ _).mp checked)
      subst returned
      let first := resumed source frame sp name (U256Value.tuple words)
      have firstCell : first.memory (frame + 16#64) = .word (sp - 1#64) := by
        change StoreWord.put source.memory (frame + 16#64) (sp - 1#64) (frame + 16#64) = _
        exact if_pos rfl
      have firstEffect := PrefixEffect.resumed source frame sp name (U256Value.tuple words) positive
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
      rcases ih first firstPost (sp - 1#64) nodup.2 code ev mapped firstCell exceptionShape continuationRun with failed | completed
      · obtain ⟨actualId, actualPayload, fitsNames, effect, zeroCell⟩ := failed
        have restored := (firstEffect.trans effect).restore source name
        have paid : 1 + ((sp - 1#64).toNat + 1) = sp.toNat + 1 := by omega
        rw [paid] at restored
        refine Or.inl ⟨actualId, actualPayload, ?_, ?_, ?_⟩
        · simp only [List.length_cons]; omega
        · rw [scope]; exact restored
        · rw [scope]; exact zeroCell
      · obtain ⟨ready, inner, remaining, effect, readyCell, depth, cells, other, tailRun, scopeEq⟩ := completed
        have combined := firstEffect.trans effect
        have paid : 1 + names.length = (name :: names).length := by simp [Nat.add_comm]
        rw [paid] at combined
        have headCell : ready.locals.lookup (ofString name) = some (U256Value.tuple words) := by
          rw [other name (by intro later member equal; exact nodup.1 (List.mem_map.mpr ⟨later, member, equal⟩))]
          simp [first, resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
        refine Or.inr ⟨ready, inner, remaining, combined, readyCell, ?_, ?_, ?_, tailRun, ?_⟩
        · simp only [List.length_cons]; omega
        · intro key member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨words, headCell⟩
          · exact cells key member
        · intro key away
          exact (other key (by intro later member; exact away later (by simp [member]))).trans
            (resumed_other_exception source frame sp name key (U256Value.tuple words) (away name (by simp)))
        · rw [scope]; exact scopeEq

end InitECandidate.Solver.GasBudget.StackPop

#print axioms InitECandidate.Solver.GasBudget.StackPop.pops_typed_exception
