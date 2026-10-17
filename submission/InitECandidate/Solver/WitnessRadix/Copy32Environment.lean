import InitECandidate.Solver.WitnessRadix.Copy32Call

namespace InitECandidate.Solver.WitnessRadix.Copy32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def formals : List (MlS × ShapeHOL) :=
  [(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)]

def values (dst src : BitVec 64) : List (ValueHOL 64) :=
  [.val (.word dst), .val (.word src), .val (.word 32#64)]

def rawLocals (dst src : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "n" then some (.val (.word 32#64))
  else if name = ofString "src" then some (.val (.word src))
  else if name = ofString "dst" then some (.val (.word dst)) else none

theorem raw_lookup (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (dst src : BitVec 64) (code : codeFn (ofString "memcpy") = some (formals, body, .one)) :
    lookupCodeHOLExact codeFn (ofString "memcpy") (values dst src) = some (body, rawLocals dst src, .one) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values dst src).length ∧
      ((formals.zip (values dst src)).all
        (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  simp only [lookupCodeHOLExact, code, valid, ↓reduceIte]
  rfl

/-- The actual fixed memcpy code entry supplies all callee ABI facts, with no
assumed successful call or successful execution. -/
theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (dst src : BitVec 64) (code : codeFn (ofString "memcpy") = some (formals, body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "memcpy") (values dst src) = some (body, callee, .one) ∧
      callee.lookup (ofString "dst") = some (.val (.word dst)) ∧
      callee.lookup (ofString "src") = some (.val (.word src)) ∧
      callee.lookup (ofString "n") = some (.val (.word 32#64)) ∧
      callee.lookup (ofString "i") = none := by
  have raw := raw_lookup codeFn dst src code
  cases lookup : lookupCodeHOLFinite codeFn (ofString "memcpy") (values dst src) with
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
      · have an : ofString "dst" ≠ ofString "n" := by decide
        have ab : ofString "dst" ≠ ofString "src" := by decide
        simp [rawLocals, an, ab]
      · have bn : ofString "src" ≠ ofString "n" := by decide
        simp [rawLocals, bn]
      · simp [rawLocals]
      · have ina : ofString "i" ≠ ofString "dst" := by decide
        have inb : ofString "i" ≠ ofString "src" := by decide
        have inn : ofString "i" ≠ ofString "n" := by decide
        simp [rawLocals, ina, inb, inn]

end InitECandidate.Solver.WitnessRadix.Copy32

#print axioms InitECandidate.Solver.WitnessRadix.Copy32.environment
