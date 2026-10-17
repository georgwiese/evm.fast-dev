import InitECandidate.Solver.WitnessRadix.CopyGeneral
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.WitnessRadix.CopyGeneral
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def formals : List (MlS × ShapeHOL) := [(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)]
def values (dst src : BitVec 64) (length : Nat) : List (ValueHOL 64) :=
  [.val (.word dst), .val (.word src), .val (.word (BitVec.ofNat 64 length))]
def rawLocals (dst src : BitVec 64) (length : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "n" then some (.val (.word (BitVec.ofNat 64 length)))
  else if name = ofString "src" then some (.val (.word src))
  else if name = ofString "dst" then some (.val (.word dst)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (dst src : BitVec 64) (length : Nat)
    (code : codeFn (ofString "memcpy") = some (formals, Copy32.body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "memcpy") (values dst src length) = some (Copy32.body, callee, .one) ∧
      callee.lookup (ofString "dst") = some (.val (.word dst)) ∧
      callee.lookup (ofString "src") = some (.val (.word src)) ∧
      callee.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values dst src length).length ∧
      ((formals.zip (values dst src length)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact codeFn (ofString "memcpy") (values dst src length) = some (Copy32.body, rawLocals dst src length, .one) := by
    simp only [lookupCodeHOLExact, code, valid, ↓reduceIte]
    rfl
  obtain ⟨callee, lookup, locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee, lookup, ?_, ?_, ?_⟩
  all_goals rw [locals]; simp [rawLocals, ofString]

end InitECandidate.Solver.WitnessRadix.CopyGeneral

#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.environment
