import InitECandidate.Solver.WordToStackBound.Initialization

namespace InitECandidate.Solver.WordToStackBound
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.InitializationStateRel
open Flapjack.WordToStackProofs.CompCorrect

/-- Quantitative entry simulation of the actual native compiler. The fixed
guest must discharge the complete initialization, code and stack-space guards. -/
theorem compiledEntry {width : Nat} [NeZero width] {C F : Type}
    (asmConf : AsmConfigExact width) (limit : Nat)
    (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (t : StackSemStateFiniteExact width C F) (k start : Nat)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : t.code = sptFromAList (compileNative asmConf false code).2.2.2 ∧
      k = asmConf.regCount - (5 + asmConf.avoidRegs.length) ∧
      initStateOk asmConf k t coracle ∧
      panPropsALookupEq raiseStubLocation code = none ∧
      panPropsALookupEq storeConstsStubLocation code = none ∧
      (compileNative asmConf false code).1 <+: t.bitmaps ∧
      (∀ entry ∈ code, flatExpConventions entry.2.2 = true ∧
        postAllocConventionsHOL (asmConf.regCount - (5 + asmConf.avoidRegs.length))
          entry.2.2 = true))
    (safe : CodeSafe limit (sptFromAList code))
    (result : Option (WordSemResult width))
    (post : WordSemStateFiniteExact width (Nat × C) F)
    (run : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      (makeInit asmConf k t (sptFromAList code) coracle) = (result, post))
    (notError : result ≠ some .error)
    (space : post.stackMax.getD (post.stackLimit + 1) ≤ post.stackLimit) :
    ∃ extra targetPost,
      extra ≤ (2 * limit) * (t.clock - post.clock) ∧
      t.clock + extra ≤ (2 * limit + 1) * t.clock ∧
      StackSemEvaluate.evaluate (.call none (.inl start) none,
        {t with clock := t.clock + extra}) = (result.map compileResult, targetPost) ∧
      targetPost.ffi = post.ffi ∧ targetPost.clock = post.clock := by
  exact Entry.entrySimulation asmConf limit start k
    (makeInit asmConf k t (sptFromAList code) coracle) post t [] result safe
    (initialRelation asmConf code t k coracle h) run notError space

end InitECandidate.Solver.WordToStackBound
#print axioms InitECandidate.Solver.WordToStackBound.compiledEntry
