import InitECandidate.Solver.Input.DeclarationGlobals

namespace InitECandidate.Solver.Input.DeclarationCode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def globalNames : List (DeclHOL 64) → List MlS
  | [] => []
  | .decl _ name _ :: rest => name :: globalNames rest
  | _ :: rest => globalNames rest

def ZeroGlobals (program : List (DeclHOL 64)) : Prop :=
  ∀ shape name expression,DeclHOL.decl shape name expression ∈ program → expression = .const 0#64

def zeroGlobalsCheck (program : List (DeclHOL 64)) : Bool :=
  program.all fun declaration => match declaration with
    | .decl _ _ expression => match expression with | .const word => word == 0#64 | _ => false
    | _ => true

theorem zero_check (program : List (DeclHOL 64)) (checked : zeroGlobalsCheck program = true) : ZeroGlobals program := by
  intro shape name expression member
  have selected := List.all_eq_true.mp checked (.decl shape name expression) member
  cases expression <;> simp_all

theorem final_global_zero (program : List (DeclHOL 64)) (zero : ZeroGlobals program) (key : MlS) :
    finalGlobal key program (some (.val (.word 0#64))) = some (.val (.word 0#64)) := by
  induction program with
  | nil => rfl
  | cons declaration rest ih =>
    have tailZero : ZeroGlobals rest := fun shape name expression member => zero shape name expression (List.mem_cons_of_mem _ member)
    cases declaration with
    | decl shape name expression =>
      have actual := zero shape name expression (by simp)
      rw [actual]
      simp only [finalGlobal,nextGlobal]
      split <;> exact ih tailZero
    | name _ _ | function _ | exnDecl _ _ => exact ih tailZero

theorem final_global_defined (program : List (DeclHOL 64)) (zero : ZeroGlobals program) (key : MlS)
    (member : key ∈ globalNames program) (incoming : Option (ValueHOL 64)) :
    finalGlobal key program incoming = some (.val (.word 0#64)) := by
  induction program generalizing incoming with
  | nil => cases member
  | cons declaration rest ih =>
    have tailZero : ZeroGlobals rest := fun shape name expression member => zero shape name expression (List.mem_cons_of_mem _ member)
    cases declaration with
    | decl shape name expression =>
      have actual := zero shape name expression (by simp)
      rw [actual]
      by_cases same : name = key
      · subst name
        simp only [finalGlobal,nextGlobal,beq_self_eq_true,↓reduceIte]
        exact final_global_zero rest tailZero key
      · have tailMember : key ∈ globalNames rest := by
          simp only [globalNames,List.mem_cons] at member
          rcases member with equal | found
          · exact False.elim (same equal.symm)
          · exact found
        simpa [finalGlobal,nextGlobal,same] using ih tailZero tailMember incoming
    | name _ _ | function _ | exnDecl _ _ => exact ih tailZero member incoming

/-- Every declared scalar zero global is installed by the actual successful
pass, for arbitrary incoming globals and without distinctness assumptions. -/
theorem zero_global_lookup {F : Type} (source target : PanSemStateFiniteExact 64 F) [DecidablePred source.memaddrs]
    (program : List (DeclHOL 64)) (zero : ZeroGlobals program)
    (run : evaluateDeclsHOLFinite source program = some target) (key : MlS) (member : key ∈ globalNames program) :
    target.globals.lookup key = some (.val (.word 0#64)) := by
  have literal : LiteralGlobal key program := fun shape expression found => ⟨0#64,zero shape key expression found⟩
  rw [global_lookup source target program key literal run,final_global_defined program zero key member]

end InitECandidate.Solver.Input.DeclarationCode

#print axioms InitECandidate.Solver.Input.DeclarationCode.zero_check
#print axioms InitECandidate.Solver.Input.DeclarationCode.final_global_zero
#print axioms InitECandidate.Solver.Input.DeclarationCode.final_global_defined
#print axioms InitECandidate.Solver.Input.DeclarationCode.zero_global_lookup
