import InitECandidate.Solver.MutableTable.TableRuntime.State
import InitECandidate.Solver.WitnessRadix.TableEnvironment

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (kind : KeyHash.Kind) (capacity : Nat) : List (ValueHOL 64) := [.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind))), .val (.word (BitVec.ofNat 64 capacity))]
def rawLocals (kind : KeyHash.Kind) (capacity : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "cap" then some (.val (.word (BitVec.ofNat 64 capacity)))
  else if name = ofString "key_len" then some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind)))) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (kind : KeyHash.Kind) (capacity : Nat)
    (code : codeFn (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "htab_new") (values kind capacity) = some (TableNew.body, callee, .one) ∧
      callee.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind)))) ∧
      callee.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity))) := by
  have valid : (TableNew.formals.map Prod.fst).Nodup ∧ TableNew.formals.length = (values kind capacity).length ∧
      ((TableNew.formals.zip (values kind capacity)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [TableNew.formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact codeFn (ofString "htab_new") (values kind capacity) =
      some (TableNew.body, rawLocals kind capacity, .one) := by
    simp only [lookupCodeHOLExact, code, valid, ↓reduceIte]
    rfl
  obtain ⟨callee, lookup, locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee, lookup, ?_, ?_⟩
  · rw [locals]
    have different : ofString "key_len" ≠ ofString "cap" := by decide
    simp [rawLocals, different]
  · rw [locals]; simp [rawLocals]

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.environment
