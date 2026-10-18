import InitECandidate.Solver.Input.DeclarationCode

namespace InitECandidate.Solver.Input.DeclarationCode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def exceptions {width : Nat} [NeZero width] : List (DeclHOL width) → List (MlS × ShapeHOL)
  | [] => []
  | .exnDecl name shape :: rest => (name, shape) :: exceptions rest
  | _ :: rest => exceptions rest

/-- The actual declaration evaluator installs the literal exception shapes.
The theorem retains arbitrary incoming exception entries and all failure checks. -/
theorem exception_lookup {width : Nat} {F : Type} [NeZero width]
    (source : PanSemStateFiniteExact width F) [hsource : DecidablePred source.memaddrs]
    (program : List (DeclHOL width)) (target : PanSemStateFiniteExact width F)
    (run : evaluateDeclsHOLFinite source program = some target) (key : MlS) :
    target.eshapes.lookup key =
      match lastEntry (exceptions program) key with
      | some value => some value
      | none => source.eshapes.lookup key := by
  induction program generalizing source with
  | nil =>
      simp only [evaluateDeclsHOLFinite, Option.some.injEq] at run
      subst target
      rfl
  | cons declaration rest ih =>
      cases declaration with
      | name name fields => exact ih source run
      | decl shape name expression =>
          simp only [evaluateDeclsHOLFinite] at run
          letI : DecidablePred (emptyLocalsHOLFinite source).memaddrs := hsource
          cases read : evalHOLFinite (emptyLocalsHOLFinite source) expression with
          | none => simp [read] at run
          | some value =>
              by_cases typed : shapeEqHOL shape (shapeOfHOLExact value) = true
              · simp only [read, if_pos typed] at run
                letI : DecidablePred (setGlobalHOLFinite name value source).memaddrs := hsource
                exact ih (setGlobalHOLFinite name value source) run
              · simp [read, typed] at run
      | function declaration =>
          simp only [evaluateDeclsHOLFinite] at run
          by_cases valid : (declaration.params.all (fun parameter => isWfShapeExactHOL source.structs parameter.2) &&
              isWfShapeExactHOL source.structs declaration.returnShape) = true
          · simp only [if_pos valid] at run
            exact ih {source with code := source.code.update (declaration.name,
              (declaration.params, declaration.body, declaration.returnShape))} run
          · simp [valid] at run
      | exnDecl name shape =>
          simp only [evaluateDeclsHOLFinite] at run
          by_cases valid : ((source.eshapes.lookup name).isNone && isWfShapeExactHOL source.structs shape) = true
          · simp only [if_pos valid] at run
            rw [ih {source with eshapes := source.eshapes.update (name, shape)} run]
            simp only [exceptions, lastEntry]
            cases lastEntry (exceptions rest) key with
            | some value => rfl
            | none =>
                by_cases same : (name == key) = true <;>
                  simp [HolFiniteMapExact.lookup_update, FUPDATE, same]
          · simp [valid] at run

theorem exception_installed {width : Nat} {F : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width F) [DecidablePred source.memaddrs]
    (program : List (DeclHOL width))
    (run : evaluateDeclsHOLFinite source program = some target)
    (name : MlS) (shape : ShapeHOL)
    (found : lastEntry (exceptions program) name = some shape) :
    target.eshapes.lookup name = some shape := by
  rw [exception_lookup source program target run name, found]

end InitECandidate.Solver.Input.DeclarationCode

#print axioms InitECandidate.Solver.Input.DeclarationCode.exception_lookup
#print axioms InitECandidate.Solver.Input.DeclarationCode.exception_installed
