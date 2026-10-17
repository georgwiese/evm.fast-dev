import InitECandidate.Solver.WitnessRadix.MemeqCall

namespace InitECandidate.Solver.WitnessRadix.Memeq32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def formals : List (MlS × ShapeHOL) :=
  [(ofString "a", .one), (ofString "b", .one), (ofString "n", .one)]

def values (a b : BitVec 64) : List (ValueHOL 64) :=
  [.val (.word a), .val (.word b), .val (.word 32#64)]

def rawLocals (a b : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "n" then some (.val (.word 32#64))
  else if name = ofString "b" then some (.val (.word b))
  else if name = ofString "a" then some (.val (.word a)) else none

theorem raw_lookup (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (a b : BitVec 64) (code : codeFn (ofString "memeq") = some (formals, body, .one)) :
    lookupCodeHOLExact codeFn (ofString "memeq") (values a b) = some (body, rawLocals a b, .one) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values a b).length ∧
      ((formals.zip (values a b)).all
        (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  simp only [lookupCodeHOLExact, code, valid, ↓reduceIte]
  rfl

/-- The actual fixed memeq code entry supplies all callee ABI facts, with no
assumed successful call or successful execution. -/
theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (a b : BitVec 64) (code : codeFn (ofString "memeq") = some (formals, body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "memeq") (values a b) = some (body, callee, .one) ∧
      callee.lookup (ofString "a") = some (.val (.word a)) ∧
      callee.lookup (ofString "b") = some (.val (.word b)) ∧
      callee.lookup (ofString "n") = some (.val (.word 32#64)) ∧
      callee.lookup (ofString "i") = none := by
  have raw := raw_lookup codeFn a b code
  cases lookup : lookupCodeHOLFinite codeFn (ofString "memeq") (values a b) with
  | none =>
      have absent := (lookupCodeHOLFinite_eq_none_iff codeFn _ _).mp lookup
      rw [raw] at absent
      cases absent
  | some data =>
      obtain ⟨body', callee, shape⟩ := data
      have eq := lookupCodeHOLFinite_eq_some codeFn _ _ body' callee shape lookup
      rw [raw] at eq
      simp only [Option.some.injEq, Prod.mk.injEq] at eq
      obtain ⟨bodyEq, localsEq, shapeEq⟩ := eq
      subst body'
      subst shape
      refine ⟨callee, rfl, ?_, ?_, ?_, ?_⟩
      all_goals rw [← localsEq]
      · have an : ofString "a" ≠ ofString "n" := by decide
        have ab : ofString "a" ≠ ofString "b" := by decide
        simp [rawLocals, an, ab]
      · have bn : ofString "b" ≠ ofString "n" := by decide
        simp [rawLocals, bn]
      · simp [rawLocals]
      · have ina : ofString "i" ≠ ofString "a" := by decide
        have inb : ofString "i" ≠ ofString "b" := by decide
        have inn : ofString "i" ≠ ofString "n" := by decide
        simp [rawLocals, ina, inb, inn]

end InitECandidate.Solver.WitnessRadix.Memeq32

#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.environment
