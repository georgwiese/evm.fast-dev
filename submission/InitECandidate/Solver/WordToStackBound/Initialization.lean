import InitECandidate.Solver.WordToStackBound.Entry
import Flapjack.Compiler.Backend.WordToStack.Proofs.InitializationStateRel
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileLookup
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileKeys
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Misc.Sptree.ToAList


namespace InitECandidate.Solver.WordToStackBound
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.InitializationStateRel

private theorem sptAListLookup_eq {α : Type} (key : Nat) :
    ∀ entries : List (Nat × α), sptAListLookup key entries = panPropsALookupEq key entries
  | [] => rfl
  | (other, value) :: entries => by
      simp only [sptAListLookup, panPropsALookupEq, sptAListLookup_eq key entries]
      by_cases h : key = other
      · subst h; simp
      · simp [h, Ne.symm h]

private theorem mem_of_lookup {α : Type} {key : Nat} {value : α} :
    ∀ {entries : List (Nat × α)}, panPropsALookupEq key entries = some value →
      (key, value) ∈ entries
  | [], h => by simp [panPropsALookupEq] at h
  | (other, v) :: entries, h => by
      simp only [panPropsALookupEq] at h
      by_cases ho : other = key
      · subst ho
        simp only [decide_true, if_true, Option.some.injEq] at h
        subst h
        exact List.mem_cons_self
      · simp only [ho, decide_false, Bool.false_eq_true, if_false] at h
        exact List.mem_cons_of_mem _ (mem_of_lookup h)

-- Derive the full initial relation from the actual native compilation.
theorem initialRelation {width : Nat} [NeZero width] {C F : Type}
    (asmConf : AsmConfigExact width) (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (t : StackSemStateFiniteExact width C F) (k : Nat)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : t.code = sptFromAList (compileNative asmConf false code).2.2.2 ∧
      k = asmConf.regCount - (5 + asmConf.avoidRegs.length) ∧
      initStateOk asmConf k t coracle ∧
      panPropsALookupEq raiseStubLocation code = none ∧
      panPropsALookupEq storeConstsStubLocation code = none ∧
      (compileNative asmConf false code).1 <+: t.bitmaps ∧
      (∀ entry ∈ code, flatExpConventions entry.2.2 = true ∧
        postAllocConventionsHOL (asmConf.regCount - (5 + asmConf.avoidRegs.length))
          entry.2.2 = true)) :
    stateRel asmConf k 0 0
      (makeInit asmConf k t (sptFromAList code) coracle) t [] 0 := by
  classical
  obtain ⟨codeEq, kEq, ok, noRaise, noStore, bitmapsPrefix, conventions⟩ := h
  subst kEq
  rcases compiled : compileWordToStackNative asmConf false
      (asmConf.regCount - (5 + asmConf.avoidRegs.length)) code (.list [4], 1) with
    ⟨bodies, frames, output, nextIndex⟩
  simp only [compileNative, Bool.false_eq_true, if_false, compiled] at codeEq bitmapsPrefix
  have keys := mapFstCompileWordToStack asmConf false _ code (.list [4], 1) bodies
    (frames, (output, nextIndex)) compiled
  have stubsDistinct : raiseStubLocation ≠ storeConstsStubLocation := by
    simp [raiseStubLocation, storeConstsStubLocation, wordNumStubs]
  have related : stateRel asmConf (asmConf.regCount - (5 + asmConf.avoidRegs.length)) 0 0
      (makeInit asmConf (asmConf.regCount - (5 + asmConf.avoidRegs.length)) t (sptFromAList code)
        coracle : WordSemStateFiniteExact width (Nat × C) F)
      t [] 0 := by
    apply initStateOkImpliesStateRel
    refine ⟨?_, ?_, ?_, ?_, ok⟩
    · rw [codeEq, sptLookup_sptFromAList, sptAListLookup_eq]
      simp [panPropsALookupEq]
    · rw [codeEq, sptLookup_sptFromAList, sptAListLookup_eq]
      simp [panPropsALookupEq, stubsDistinct]
    · intro n wordProg argumentCount lookup
      rw [sptLookup_sptFromAList, sptAListLookup_eq] at lookup
      have member := mem_of_lookup lookup
      obtain ⟨flat, allocated⟩ := conventions _ member
      obtain ⟨bs, i, bs2, i2, frame, body, compileRun, b1, b2, b3, bodyLookup⟩ :=
        compileWordToStackImpALookup asmConf false _ code (.list [4]) 1 bodies frames output
          nextIndex n argumentCount wordProg t.bitmaps compiled lookup
          (by simp [appListAppend, appendAux]) (by simp [appListAppend, appendAux])
          (by simpa [appListAppend, appendAux] using bitmapsPrefix)
      refine ⟨allocated, flat, bs, i, bs2, i2, frame, body, compileRun, b1, b2, b3, ?_⟩
      have notRaise : n ≠ raiseStubLocation := by
        rintro rfl
        rw [noRaise] at lookup
        cases lookup
      have notStore : n ≠ storeConstsStubLocation := by
        rintro rfl
        rw [noStore] at lookup
        cases lookup
      rw [codeEq, sptLookup_sptFromAList, sptAListLookup_eq]
      simp [panPropsALookupEq, Ne.symm notRaise, Ne.symm notStore, bodyLookup]
    · rw [codeEq, sptDomainFromAList, sptDomainFromAList]
      funext x
      simp only [List.map_cons, List.mem_cons, keys]
  exact related

end InitECandidate.Solver.WordToStackBound
#print axioms InitECandidate.Solver.WordToStackBound.initialRelation
