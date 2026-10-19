import InitECandidate.Solver.Rlp.HeaderCost
import InitECandidate.Solver.Input.LocalEffectsScoped

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (pointer length : BitVec 64) : List (ValueHOL 64) := [.val (.word pointer),.val (.word length)]
def rawLocals (pointer length : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "len" then some (.val (.word length)) else if name=ofString "p" then some (.val (.word pointer)) else none

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (pointer length : BitVec 64) (known : table (ofString "rlp_item_header")=some (formals,body,resultShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "rlp_item_header") (values pointer length)=some (body,callee,resultShape) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) ∧ callee.lookup (ofString "len")=some (.val (.word length)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values pointer length).length ∧
      ((formals.zip (values pointer length)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact table (ofString "rlp_item_header") (values pointer length)=some (body,rawLocals pointer length,resultShape) := by
    simp only [lookupCodeHOLExact,known,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup table _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  · rw [locals]
    simp [rawLocals,show ofString "p"≠ofString "len" from by decide]
  · rw [locals]
    simp [rawLocals]

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer length))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "rlp_item_header") arguments)).2.clock≤11 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := environment source.code.lookup pointer length (original_code source.code installed)
  exact Input.ClockCost.call_current source destination (ofString "rlp_item_header") arguments _ body callee resultShape 10 args called
    (body_cost (callEntryStateHOLFinite source callee) pointer pointerLocal installed)

theorem scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer length))
    (installed : Input.OriginalCode.Installed source.code) (tailCost : Input.ClockCost.Bound source.code continuation tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall name resultShape (ofString "rlp_item_header") arguments continuation)).2.clock≤10+tailPrice+1 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := environment source.code.lookup pointer length (original_code source.code installed)
  exact Input.ClockCost.scoped_current source name resultShape (ofString "rlp_item_header") arguments _ body continuation callee resultShape 10 tailPrice args called
    (body_cost (callEntryStateHOLFinite source callee) pointer pointerLocal installed) tailCost

set_option maxRecDepth 10000 in
theorem readonly (code) (installed : Input.OriginalCode.Installed code) : Input.LocalEffects.Preserves code body := by
  simp only [body,Guest.guestFn_rlp_item_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat first
    | apply Input.LocalEffects.sequence
    | apply Input.LocalEffects.declared
    | apply Input.LocalEffects.conditional
    | exact Input.LocalEffects.returned code _
    | exact Input.LocalEffects.skip code
    | exact Input.LocalEffects.call_body code (some none) (ofString "rlp_fail") _ Fail.formals Fail.body .one (Fail.original_code code installed) (Fail.readonly code)
    | apply Input.LocalEffects.scoped_body code (ofString "n") .one (ofString "rlp_read_length") _ _ ReadLength.formals ReadLength.body .one
        (ReadLength.original_code code installed) (ReadLength.readonly code installed)

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.environment
#print axioms InitECandidate.Solver.Rlp.Header.call_cost
#print axioms InitECandidate.Solver.Rlp.Header.scoped_cost
#print axioms InitECandidate.Solver.Rlp.Header.readonly
