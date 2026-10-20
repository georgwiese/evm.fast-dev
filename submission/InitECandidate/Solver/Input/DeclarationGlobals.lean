import InitECandidate.Solver.Input.DeclarationCode

namespace InitECandidate.Solver.Input.DeclarationCode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Only declarations of the selected global need literal initializers.
All unrelated global expressions retain their actual evaluator checks. -/
def LiteralGlobal (key : MlS) (program : List (DeclHOL 64)) : Prop :=
  ∀ shape expression,DeclHOL.decl shape key expression ∈ program → ∃ word,expression = .const word

def literalGlobalCheck (key : MlS) (program : List (DeclHOL 64)) : Bool :=
  program.all fun declaration => match declaration with
    | .decl _ name expression => if name == key then match expression with | .const _ => true | _ => false else true
    | _ => true

theorem literal_check (key : MlS) (program : List (DeclHOL 64)) (checked : literalGlobalCheck key program = true) :
    LiteralGlobal key program := by
  intro shape expression member
  have selected := List.all_eq_true.mp checked (.decl shape key expression) member
  simp only [if_pos (Eq.refl key)] at selected
  cases expression <;> simp_all

def nextGlobal (key : MlS) (declaration : DeclHOL 64) (value : Option (ValueHOL 64)) : Option (ValueHOL 64) :=
  match declaration with
  | .decl _ name expression => if name == key then match expression with | .const word => some (.val (.word word)) | _ => value else value
  | _ => value

def finalGlobal (key : MlS) : List (DeclHOL 64) → Option (ValueHOL 64) → Option (ValueHOL 64)
  | [],value => value
  | declaration :: rest,value => finalGlobal key rest (nextGlobal key declaration value)

/-- A successful real declaration pass supplies the selected literal global.
Neither successful initialization calls nor a future global map are assumed. -/
theorem global_lookup {F : Type} (source target : PanSemStateFiniteExact 64 F) [hsource : DecidablePred source.memaddrs]
    (program : List (DeclHOL 64)) (key : MlS) (literal : LiteralGlobal key program)
    (run : evaluateDeclsHOLFinite source program = some target) :
    target.globals.lookup key = finalGlobal key program (source.globals.lookup key) := by
  induction program generalizing source with
  | nil =>
    simp only [evaluateDeclsHOLFinite,Option.some.injEq] at run
    subst target
    rfl
  | cons declaration rest ih =>
    have tailLiteral : LiteralGlobal key rest := fun shape expression member => literal shape expression (List.mem_cons_of_mem _ member)
    cases declaration with
    | name name fields => exact ih source tailLiteral run
    | function declaration =>
      simp only [evaluateDeclsHOLFinite] at run
      by_cases valid : (declaration.params.all (fun parameter => isWfShapeExactHOL source.structs parameter.2) && isWfShapeExactHOL source.structs declaration.returnShape) = true
      · simp only [if_pos valid] at run
        exact ih {source with code := source.code.update (declaration.name,(declaration.params,declaration.body,declaration.returnShape))} tailLiteral run
      · simp [valid] at run
    | exnDecl name shape =>
      simp only [evaluateDeclsHOLFinite] at run
      by_cases valid : ((source.eshapes.lookup name).isNone && isWfShapeExactHOL source.structs shape) = true
      · simp only [if_pos valid] at run
        exact ih {source with eshapes := source.eshapes.update (name,shape)} tailLiteral run
      · simp [valid] at run
    | decl shape name expression =>
      by_cases same : name = key
      · subst name
        obtain ⟨word,rfl⟩ := literal shape expression (by simp)
        simp only [evaluateDeclsHOLFinite,evalHOLFinite,evalHOLExact] at run
        by_cases typed : shapeEqHOL shape (.one : ShapeHOL) = true
        · simp only [shapeOfHOLExact,if_pos typed] at run
          letI : DecidablePred (setGlobalHOLFinite key (.val (.word word)) source).memaddrs := hsource
          rw [ih (setGlobalHOLFinite key (.val (.word word)) source) tailLiteral run]
          simp [finalGlobal,nextGlobal,setGlobalHOLFinite,HolFiniteMapExact.update,FUPDATE]
        · simp [shapeOfHOLExact,typed] at run
      · simp only [evaluateDeclsHOLFinite] at run
        letI : DecidablePred (emptyLocalsHOLFinite source).memaddrs := hsource
        cases read : evalHOLFinite (emptyLocalsHOLFinite source) expression with
        | none => simp [read] at run
        | some value =>
          by_cases typed : shapeEqHOL shape (shapeOfHOLExact value) = true
          · simp only [read,if_pos typed] at run
            letI : DecidablePred (setGlobalHOLFinite name value source).memaddrs := hsource
            rw [ih (setGlobalHOLFinite name value source) tailLiteral run]
            simp [finalGlobal,nextGlobal,same,setGlobalHOLFinite,HolFiniteMapExact.update,FUPDATE]
          · simp [read,typed] at run

end InitECandidate.Solver.Input.DeclarationCode

#print axioms InitECandidate.Solver.Input.DeclarationCode.global_lookup
#print axioms InitECandidate.Solver.Input.DeclarationCode.literal_check
