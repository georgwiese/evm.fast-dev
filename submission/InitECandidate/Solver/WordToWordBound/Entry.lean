import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSemantics

namespace InitECandidate.Solver.WordToWordBound
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordProps
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Encoders.Asm

/-- Retain clock and stackMax from the existing Pancake-facing simulation,
including the permutation transport back to the actual source run. -/
theorem entryRunsAgree {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (l : Spt (Nat × WordLangProgHOL (BitVec width)))
    (start k : Nat) (hrel : codeRel s.code l) (hnic : noInstallCode s.code)
    (hnac : noAllocCode s.code) (hnmc : noMtCode s.code) (hdom : sptDomain s.code = sptDomain l)
    (hgc : Compiler.Backend.WordSimp.gcFunConstOk s.gcFun) (hstack : s.stack = [])
    (hne : (evaluate (.call none (some start) [0] none) { s with clock := k }).1 ≠ some .error) :
    (evaluate (.call none (some start) [0] none) { s with clock := k, code := l }).1 =
        (evaluate (.call none (some start) [0] none) { s with clock := k }).1 ∧
      (evaluate (.call none (some start) [0] none) { s with clock := k, code := l }).2.clock =
        (evaluate (.call none (some start) [0] none) { s with clock := k }).2.clock ∧
      (evaluate (.call none (some start) [0] none) { s with clock := k, code := l }).2.ffi =
        (evaluate (.call none (some start) [0] none) { s with clock := k }).2.ffi ∧
      (evaluate (.call none (some start) [0] none) { s with clock := k, code := l }).2.stackMax =
        (evaluate (.call none (some start) [0] none) { s with clock := k }).2.stackMax := by
  let prog : WordLangProgHOL (BitVec width) := .call none (some start) [0] none
  let sk : WordSemStateFiniteExact width C F := { s with clock := k }
  obtain ⟨perm', H⟩ := panLang_compile_word_to_word_thm sk l start
    ⟨hrel, hnic, hnac, hnmc, hdom, hgc⟩
  have P3 := permute_swap_lemma3 prog sk perm' []
  rcases hE : evaluate prog sk with ⟨q, r⟩
  change (evaluate prog sk).1 ≠ some .error at hne
  rw [hE] at hne P3
  dsimp only at hne P3
  obtain ⟨perm'', stack', hP, -⟩ := P3 ⟨hne, hnac, rfl, hnic, rfl, by
    intro fr hfr
    change fr ∈ s.stack at hfr
    rw [hstack] at hfr
    cases hfr⟩
  dsimp only at H
  rw [hP] at H
  dsimp only at H
  rw [if_neg hne] at H
  rcases hT : evaluate prog { sk with code := l } with ⟨q1, r1⟩
  rw [hT] at H
  dsimp only at H
  obtain ⟨h1, h2, h3, h4⟩ := H
  exact ⟨h1, h2, h3, h4⟩


/-- The actual full Word compiler preserves the entry clock, result, FFI and
stack maximum when the input code has no Install, Alloc or MustTerminate. -/
theorem compiledEntry {width : Nat} [NeZero width] {C F : Type}
    (config : Config) (assembly : AsmConfigExact width)
    (inputs outputs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (remaining : List (Option (Spt Nat)))
    (source sourceFinal : WordSemStateFiniteExact width C F)
    (start : Nat) (result : Option (WordSemResult width))
    (compiled : compile config assembly inputs = (remaining, outputs))
    (gc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk source.gcFun)
    (noInstall : noInstallCode source.code) (noAlloc : noAllocCode source.code)
    (noMt : noMtCode source.code) (stack : source.stack = [])
    (code : source.code = sptFromAList inputs)
    (run : evaluate (.call none (some start) [0] none) source = (result, sourceFinal))
    (notError : result ≠ some .error) :
    ∃ targetFinal : WordSemStateFiniteExact width C F,
      evaluate (.call none (some start) [0] none)
        { source with code := sptFromAList outputs } = (result, targetFinal) ∧
      targetFinal.clock = sourceFinal.clock ∧ targetFinal.ffi = sourceFinal.ffi ∧
      targetFinal.stackMax = sourceFinal.stackMax := by
  have extended := code_rel_ext_word_to_word assembly inputs config remaining outputs compiled
  have noMtInputs : noMtCode (sptFromAList inputs) := code ▸ noMt
  have related := no_mt_code_rel_ext _ _ ⟨noMtInputs, extended⟩
  have domain : sptDomain (sptFromAList inputs) = sptDomain (sptFromAList outputs) := by
    have expansion := compiled
    simp only [compile, Prod.mk.injEq] at expansion
    obtain ⟨_, rfl⟩ := expansion
    funext n
    simp only [sptDomain, sptLookup_sptFromAList]
    rw [sptAListLookup_isSome_map_fullCompileSingle _ _ _ _ inputs _ (compile_zip_length config inputs)]
  rw [← code] at related domain
  have unchanged : ({ source with clock := source.clock } : WordSemStateFiniteExact width C F) = source := by
    cases source; rfl
  have agree := entryRunsAgree source (sptFromAList outputs) start source.clock related
    noInstall noAlloc noMt domain gc stack (by simpa only [unchanged, run] using notError)
  rw [unchanged, run] at agree
  rcases targetRun : evaluate (.call none (some start) [0] none)
      { source with code := sptFromAList outputs } with ⟨targetResult, targetFinal⟩
  change (evaluate (.call none (some start) [0] none)
    { source with code := sptFromAList outputs }).1 = result ∧ _ at agree
  rw [targetRun] at agree
  exact ⟨targetFinal, by simpa only [agree.1] using targetRun, agree.2⟩

end InitECandidate.Solver.WordToWordBound
#print axioms InitECandidate.Solver.WordToWordBound.entryRunsAgree
#print axioms InitECandidate.Solver.WordToWordBound.compiledEntry
