import InitECandidate.Solver.Headers.FieldProgram

namespace InitECandidate.Solver.Headers.Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem after_item_quiet (code) (kind : Kind) : Input.QuietClock.Preserves code kind.afterItem := by
  cases kind <;> simp only [Kind.afterItem,Kind.body,Kind.declaration,
    Guest.guestFn_hdr_uint_field,Guest.guestFn_hdr_bytes_field,Guest.guestFn_hdr_raw_field,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  all_goals repeat first
    | apply Input.QuietClock.sequence
    | apply Input.QuietClock.conditional
    | exact Input.QuietClock.skip code
    | exact Input.QuietClock.raised code _ _
    | exact Input.QuietClock.returned code _

/-- Every actual field-helper tail only reads memory and checks/returns
values, including on HdrErr and malformed-expression paths. -/
theorem after_item_readonly (code) (kind : Kind) : Input.LocalEffects.Preserves code kind.afterItem := by
  cases kind <;> simp only [Kind.afterItem,Kind.body,Kind.declaration,
    Guest.guestFn_hdr_uint_field,Guest.guestFn_hdr_bytes_field,Guest.guestFn_hdr_raw_field,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  all_goals repeat first
    | apply Input.LocalEffects.sequence
    | apply Input.LocalEffects.conditional
    | exact Input.LocalEffects.skip code
    | exact Input.LocalEffects.raised code _ _
    | exact Input.LocalEffects.returned code _

/-- The complete original uint/bytes/raw field body spends only its real
item-decoding caller clock. Its selected row length is current input data. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (pointer length cursor limit : BitVec 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Rlp.Header.values pointer length))
    (arena : Rlp.Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source kind.body).2.clock≤60*length.toNat+42 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item") Rlp.Item.body Rlp.Item.resultShape pointer length (Rlp.Item.original_code source.code installed)
  have entryArena := Rlp.Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  have price := Input.ClockCost.scoped_current source (ofString "it") Rlp.Item.resultShape (ofString "rlp_item") arguments _ Rlp.Item.body kind.afterItem callee Rlp.Item.resultShape
    (60*length.toNat+41) 0 args called
    (Rlp.Item.body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal entryArena fits installed)
    (Input.ClockCost.of_quiet source.code kind.afterItem (after_item_quiet source.code kind))
  rw [body_shape]
  exact price

end InitECandidate.Solver.Headers.Field

#print axioms InitECandidate.Solver.Headers.Field.after_item_quiet
#print axioms InitECandidate.Solver.Headers.Field.after_item_readonly
#print axioms InitECandidate.Solver.Headers.Field.body_cost
