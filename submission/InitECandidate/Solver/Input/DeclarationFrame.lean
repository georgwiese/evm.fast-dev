import InitECandidate.Solver.Input.DeclarationCode

namespace InitECandidate.Solver.Input.DeclarationCode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Erase precisely the three fields declaration evaluation can update. -/
def frame {width : Nat} {F : Type} [NeZero width] (source : PanSemStateFiniteExact width F) :=
  {source with globals := HolFiniteMapExact.empty, code := HolFiniteMapExact.empty, eshapes := HolFiniteMapExact.empty}

theorem declaration_frame {width : Nat} {F : Type} [NeZero width]
    (source : PanSemStateFiniteExact width F) [hsource : DecidablePred source.memaddrs]
    (program : List (DeclHOL width)) (target : PanSemStateFiniteExact width F)
    (run : evaluateDeclsHOLFinite source program = some target) : frame target = frame source := by
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
            exact ih {source with eshapes := source.eshapes.update (name, shape)} run
          · simp [valid] at run

end InitECandidate.Solver.Input.DeclarationCode

#print axioms InitECandidate.Solver.Input.DeclarationCode.declaration_frame
