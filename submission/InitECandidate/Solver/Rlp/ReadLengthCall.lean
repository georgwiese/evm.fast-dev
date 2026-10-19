import InitECandidate.Solver.Rlp.ReadLengthCost
import InitECandidate.Solver.Input.ClockCostCurrentCall
import InitECandidate.Solver.Input.ClockCostCurrentScoped

namespace InitECandidate.Solver.Rlp.ReadLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (pointer : BitVec 64) (length : Nat) : List (ValueHOL 64) :=
  [.val (.word pointer),.val (.word (BitVec.ofNat 64 length))]
def rawLocals (pointer : BitVec 64) (length : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "n" then some (.val (.word (BitVec.ofNat 64 length)))
  else if name=ofString "p" then some (.val (.word pointer)) else none

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (pointer : BitVec 64) (length : Nat) (known : table (ofString "rlp_read_length")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "rlp_read_length") (values pointer length)=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) ∧
      callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values pointer length).length ∧
      ((formals.zip (values pointer length)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact table (ofString "rlp_read_length") (values pointer length)=some (body,rawLocals pointer length,.one) := by
    simp only [lookupCodeHOLExact,known,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup table _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  · rw [locals]
    simp [rawLocals,show ofString "p"≠ofString "n" from by decide]
  · rw [locals]
    simp [rawLocals]

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (length : Nat)
    (small : length≤8) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer length))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "rlp_read_length") arguments)).2.clock≤9 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := environment source.code.lookup pointer length (original_code source.code installed)
  have priced := body_cost_eight (callEntryStateHOLFinite source callee) length small lengthLocal installed
  exact Input.ClockCost.call_current source destination (ofString "rlp_read_length") arguments _ body callee .one 8 args called priced

theorem scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (length : Nat)
    (small : length≤8) (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer length))
    (installed : Input.OriginalCode.Installed source.code)
    (tailCost : Input.ClockCost.Bound source.code continuation tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall name .one (ofString "rlp_read_length") arguments continuation)).2.clock≤8+tailPrice+1 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := environment source.code.lookup pointer length (original_code source.code installed)
  have priced := body_cost_eight (callEntryStateHOLFinite source callee) length small lengthLocal installed
  exact Input.ClockCost.scoped_current source name .one (ofString "rlp_read_length") arguments _ body continuation callee .one 8 tailPrice args called priced tailCost

theorem readonly (code) (installed : Input.OriginalCode.Installed code) : Input.LocalEffects.Preserves code body := by
  simp only [body,Guest.guestFn_rlp_read_length,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat first
    | apply Input.LocalEffects.sequence
    | apply Input.LocalEffects.declared
    | apply Input.LocalEffects.conditional
    | apply Input.LocalEffects.loop
    | exact Input.LocalEffects.assign code _ _
    | exact Input.LocalEffects.returned code _
    | exact Input.LocalEffects.skip code
    | exact Input.LocalEffects.call_body code (some none) (ofString "rlp_fail") _ Fail.formals Fail.body .one (Fail.original_code code installed) (Fail.readonly code)

end InitECandidate.Solver.Rlp.ReadLength

#print axioms InitECandidate.Solver.Rlp.ReadLength.environment
#print axioms InitECandidate.Solver.Rlp.ReadLength.call_cost
#print axioms InitECandidate.Solver.Rlp.ReadLength.scoped_cost
#print axioms InitECandidate.Solver.Rlp.ReadLength.readonly
