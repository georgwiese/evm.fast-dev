import InitECandidate.Solver.Input.OutputLoop
import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Input.Output
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def values (pointer : BitVec 64) (length : Nat) : List (ValueHOL 64) := [.val (.word pointer),.val (.word (BitVec.ofNat 64 length))]
def rawLocals (pointer : BitVec 64) (length : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "n" then some (.val (.word (BitVec.ofNat 64 length))) else if name = ofString "src" then some (.val (.word pointer)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (pointer : BitVec 64) (length : Nat)
    (known : codeFn (ofString "output_write") = some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "output_write") (values pointer length) = some (body,callee,.one) ∧
      callee.lookup (ofString "src") = some (.val (.word pointer)) ∧ callee.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values pointer length).length ∧
      ((formals.zip (values pointer length)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "output_write") (values pointer length) = some (body,rawLocals pointer length,.one) := by
    simp only [lookupCodeHOLExact,known,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ body _ .one raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]; simp [rawLocals,show ofString "src" ≠ ofString "n" from by decide]

/-- The real ignored output call pays its actual unsigned byte-loop length
plus one caller tick, including all early failures and timeouts. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (pointer : BitVec 64) (length : Nat)
    (small : length < 2^64) (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values pointer length)) :
    source.clock - (evaluateHOLFiniteState source (.call (some (none,none)) (ofString "output_write") arguments)).2.clock ≤ length + 1 := by
  obtain ⟨callee,called,src,n⟩ := environment source.code.lookup pointer length (original_code source.code installed)
  exact ClockCost.call_current source (some none) (ofString "output_write") arguments (values pointer length) body callee .one length args called
    (body_cost (callEntryStateHOLFinite source callee) length small n)

end InitECandidate.Solver.Input.Output

#print axioms InitECandidate.Solver.Input.Output.environment
#print axioms InitECandidate.Solver.Input.Output.call_cost
