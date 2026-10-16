import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallEvaluate

namespace InitECandidate.Solver.WordToStackBound
open Flapjack

/-- Extra clocks before accounting for calls. Each call's source decrement pays
for its callee and selected continuation, so calls carry zero local cost. -/
def cost {α : Type} : WordLangProgHOL α → Nat
  | .shareInst .. | .raise .. => 1
  | .seq first second => cost first + cost second
  | .ite _ _ _ first second => max (cost first) (cost second)
  | .loop _ body _ | .mustTerminate body => cost body
  | _ => 0

/-- Largest local cost of any subprogram, including call continuations. -/
def ceiling {α : Type} (program : WordLangProgHOL α) : Nat :=
  max (cost program) (match program with
    | .seq first second | .ite _ _ _ first second => max (ceiling first) (ceiling second)
    | .loop _ body _ | .mustTerminate body => ceiling body
    | .call ret _ _ handler =>
        max (match ret with | none => 0 | some (_, _, body, _, _) => ceiling body)
          (match handler with | none => 0 | some (_, body, _, _) => ceiling body)
    | _ => 0)

theorem cost_le_ceiling {α : Type} (program : WordLangProgHOL α) : cost program ≤ ceiling program := by
  cases program <;> exact Nat.le_max_left _ _

theorem seqCeiling {α : Type} (first second : WordLangProgHOL α) (limit : Nat)
    (bound : ceiling (.seq first second) ≤ limit) : ceiling first ≤ limit ∧ ceiling second ≤ limit := by
  rw [ceiling] at bound
  omega

theorem ifCeiling {α : Type} (comparison : Cmp) (register : Nat) (operand : WordRegImm α)
    (first second : WordLangProgHOL α) (limit : Nat)
    (bound : ceiling (.ite comparison register operand first second) ≤ limit) :
    ceiling first ≤ limit ∧ ceiling second ≤ limit := by
  rw [ceiling] at bound
  omega

def CodeSafe {width : Nat} [NeZero width] (limit : Nat)
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) : Prop :=
  WordProps.noInstallCode code ∧
    ∀ key arity program, sptLookup key code = some (arity, program) → ceiling program ≤ limit

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
    noInstallSubprogsHOL program = true ∧ ceiling program ≤ limit := by
  obtain ⟨key, arity, lookup⟩ := WordProps.findCode_lookup code dest args sizes args1 program space found
  exact ⟨safe.1 key arity program lookup, safe.2 key arity program lookup⟩

end InitECandidate.Solver.WordToStackBound
#print axioms InitECandidate.Solver.WordToStackBound.codeSafe_evaluate
#print axioms InitECandidate.Solver.WordToStackBound.codeSafe_findCode
#print axioms InitECandidate.Solver.WordToStackBound.cost_le_ceiling
#print axioms InitECandidate.Solver.WordToStackBound.seqCeiling
#print axioms InitECandidate.Solver.WordToStackBound.ifCeiling
