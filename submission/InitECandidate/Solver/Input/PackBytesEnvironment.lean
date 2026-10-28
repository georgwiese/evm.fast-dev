import InitECandidate.Solver.Input.PackBytesProgram
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.Input.PackBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (p : BitVec 64) (n : Nat) : List (ValueHOL 64) := [.val (.word p),.val (.word (BitVec.ofNat 64 n))]
def rawLocals (p : BitVec 64) (n : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "n" then some (.val (.word (BitVec.ofNat 64 n))) else if name=ofString "p" then some (.val (.word p)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (p : BitVec 64) (n : Nat)
    (code : codeFn (ofString "pack_bytes")=some (formals,body,returnShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "pack_bytes") (values p n)=some (body,callee,returnShape) ∧
      callee.lookup (ofString "p")=some (.val (.word p)) ∧ callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values p n).length ∧
      ((formals.zip (values p n)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "pack_bytes") (values p n)=some (body,rawLocals p n,returnShape) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,show ofString "p"≠ofString "n" from by decide],by rw [locals]; simp [rawLocals]⟩

end InitECandidate.Solver.Input.PackBytes

#print axioms InitECandidate.Solver.Input.PackBytes.environment
