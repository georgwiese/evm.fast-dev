import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallEvaluate

namespace InitECandidate.Solver.WordToStackBound
open Flapjack

/-- Straight-line extra clocks introduced by lowering. Branches take a maximum;
calls and loop reentry will pay for their repeated bodies from source clocks. -/
def cost {α : Type} : WordLangProgHOL α → Nat
  | .shareInst .. | .raise .. => 1
  | .seq first second => cost first + cost second
  | .ite _ _ _ first second => max (cost first) (cost second)
  | .loop _ body _ | .mustTerminate body => cost body
  | .call ret _ _ handler =>
      max (match ret with | none => 0 | some (_, _, body, _, _) => cost body)
        (match handler with | none => 0 | some (_, body, _, _) => cost body)
  | _ => 0

def CodeSafe {width : Nat} [NeZero width] (limit : Nat)
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) : Prop :=
  WordProps.noInstallCode code ∧
    ∀ key arity program, sptLookup key code = some (arity, program) → cost program ≤ limit

theorem codeSafe_evaluate {width : Nat} [NeZero width] {C F : Type}
    {limit : Nat} {program : WordLangProgHOL (BitVec width)}
    {source post : WordSemStateFiniteExact width C F} {result : Option (WordSemResult width)}
    (safe : CodeSafe limit source.code) (supported : noInstallSubprogsHOL program = true)
    (run : WordSemStateFiniteExact.evaluate program source = (result, post)) :
    CodeSafe limit post.code := by
  have equal := WordSemStateFiniteExact.noInstallEvaluateConstCode program source result post
    ⟨run, supported, safe.1⟩
  rw [← equal]
  exact safe

theorem codeSafe_findCode {width : Nat} [NeZero width] {limit : Nat}
    {code : Spt (Nat × WordLangProgHOL (BitVec width))} {dest : Option Nat}
    {args args1 : List (WordLocW width)} {sizes : Spt Nat}
    {program : WordLangProgHOL (BitVec width)} {space : Option Nat}
    (safe : CodeSafe limit code)
    (found : wordSemFindCode dest args code sizes = some (args1, program, space)) :
    noInstallSubprogsHOL program = true ∧ cost program ≤ limit := by
  obtain ⟨key, arity, lookup⟩ := WordProps.findCode_lookup code dest args sizes args1 program space found
  exact ⟨safe.1 key arity program lookup, safe.2 key arity program lookup⟩

end InitECandidate.Solver.WordToStackBound
#print axioms InitECandidate.Solver.WordToStackBound.codeSafe_evaluate
#print axioms InitECandidate.Solver.WordToStackBound.codeSafe_findCode
