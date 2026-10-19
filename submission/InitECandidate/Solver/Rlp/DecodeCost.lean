import InitECandidate.Solver.Rlp.ItemCost

namespace InitECandidate.Solver.Rlp.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "rlp_item") arguments)).2.clock≤60*length.toNat+42 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item") body resultShape pointer length (original_code source.code installed)
  exact Input.ClockCost.call_current source destination (ofString "rlp_item") arguments _ body callee resultShape (60*length.toNat+41) args called
    (body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed)

end InitECandidate.Solver.Rlp.Item

namespace InitECandidate.Solver.Rlp.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_rlp_decode_fully with | .function fn=>progToHOL fn.body | _=>.skip
def arguments : List (ExpHOL 64) := [localVar "p",localVar "len"]
def afterItem : ProgHOL 64 := .seq
  (.ite (.cmp .notEqual (.rfield 3 (localVar "it")) (localVar "len")) (Header.fail 6#64) .skip) (.return (localVar "it"))

theorem body_shape : body=.decCall (ofString "it") Item.resultShape (ofString "rlp_item") arguments afterItem := by
  simp only [body,arguments,afterItem,Item.resultShape,Header.fail,localVar,Guest.guestFn_rlp_decode_fully,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "rlp_decode_fully")=some (Header.formals,body,Item.resultShape) := by
  have checked := Input.OriginalCode.indexed code installed 96 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_rlp_decode_fully) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Header.formals,Item.resultShape,
    Guest.guestFn_rlp_decode_fully,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem after_item_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code afterItem 1 :=
  Fail.guard_price code installed _ _ _ 0 (Input.ClockCost.returned code _)

theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤60*length.toNat+43 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item") Item.body Item.resultShape pointer length (Item.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length) := by
    simp [arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  rw [body_shape]
  have price := Input.ClockCost.scoped_current source (ofString "it") Item.resultShape (ofString "rlp_item") arguments _ Item.body afterItem callee Item.resultShape (60*length.toNat+41) 1 args called
    (Item.body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed)
    (after_item_price source.code installed)
  omega

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "rlp_decode_fully") expressions)).2.clock≤60*length.toNat+44 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_decode_fully") body Item.resultShape pointer length (original_code source.code installed)
  exact Input.ClockCost.call_current source destination (ofString "rlp_decode_fully") expressions _ body callee Item.resultShape (60*length.toNat+43) args called
    (body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed)

end InitECandidate.Solver.Rlp.Decode

#print axioms InitECandidate.Solver.Rlp.Item.call_cost
#print axioms InitECandidate.Solver.Rlp.Decode.body_shape
#print axioms InitECandidate.Solver.Rlp.Decode.original_code
#print axioms InitECandidate.Solver.Rlp.Decode.after_item_price
#print axioms InitECandidate.Solver.Rlp.Decode.body_cost
#print axioms InitECandidate.Solver.Rlp.Decode.call_cost
