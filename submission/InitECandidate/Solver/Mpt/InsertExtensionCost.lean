import InitECandidate.Solver.Mpt.InsertSuffixCost
import InitECandidate.Solver.Mpt.CommonPrefixCall
import InitECandidate.Solver.Input.ClockCostCurrentScoped
import InitECandidate.Solver.Input.ClockCostDeclaredReached

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every original extension-comparison/split outcome has a fixed source
allowance once the current remaining query is bounded by64 nibbles. -/
theorem extension_prefix_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (segment oldLength key level length : BitVec 64) (bounded : length.toNat≤64) (before : level.toNat≤length.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (oldLengthCell : source.locals.lookup (ofString "sl")=some (.val (.word oldLength)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length))) :
    source.clock-(evaluateHOLFiniteState source extensionPrefixScope).2.clock≤306 := by
  have subtraction : (length-level).toNat=length.toNat-level.toNat:=BitVec.toNat_sub_of_le (by rwa [BitVec.le_def])
  have small : min oldLength.toNat (length-level).toNat≤64:=by rw [subtraction]; omega
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) prefixArguments=
      some (CommonPrefix.values segment oldLength (key+level) (length-level)):=by
    simp [prefixArguments,queryPointer,queryLength,CommonPrefix.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,
      segmentCell,oldLengthCell,keyCell,levelCell,lengthCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨callee,called,aCell,alCell,bCell,blCell⟩:=CommonPrefix.environment source.code.lookup segment oldLength (key+level) (length-level) (CommonPrefix.original_code source.code installed)
  have price:=CommonPrefix.body_cost (callEntryStateHOLFinite source callee) oldLength (length-level) small installed alCell blCell
  have priced : (callEntryStateHOLFinite source callee).clock-(evaluateHOLFiniteState (callEntryStateHOLFinite source callee) CommonPrefix.body).2.clock≤65:=price.trans (by omega)
  rw [extension_shapes.2.2.1]
  exact Input.ClockCost.scoped_current source (ofString "pl") .one (ofString "common_prefix_length") prefixArguments _ CommonPrefix.body extensionPrefixChoice callee .one 65 240
    args called priced (extension_prefix_choice_price source.code installed)

theorem extension_length_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (segment key level length : BitVec 64) (bounded : length.toNat≤64) (before : level.toNat≤length.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length))) :
    source.clock-(evaluateHOLFiniteState source extensionLengthScope).2.clock≤306 := by
  rw [extension_shapes.2.1]
  apply Input.ClockCost.declared_reached_current
  intro loaded _read checked
  cases loaded with
  | val payload=>
    cases payload with
    | word oldLength=>
      let current:=QueryBranch.bind source "sl" oldLength
      exact extension_prefix_cost current segment oldLength key level length bounded before installed
        ((bind_lookup_other source "sl" "seg" oldLength (by decide)).trans segmentCell) (bind_lookup_same source "sl" oldLength)
        ((bind_lookup_other source "sl" "key" oldLength (by decide)).trans keyCell)
        ((bind_lookup_other source "sl" "level" oldLength (by decide)).trans levelCell)
        ((bind_lookup_other source "sl" "klen" oldLength (by decide)).trans lengthCell)
  | rStruct fields=>simp [shapeEqHOL,shapeOfHOLExact] at checked
  | nStruct name fields=>simp [shapeEqHOL,shapeOfHOLExact] at checked

/-- Uniform across arbitrary stored node fields, unmapped reads, actual
mismatches, helper failures and short clocks; no later success is assumed. -/
theorem extension_scope_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (key level length : BitVec 64) (bounded : length.toNat≤64) (before : level.toNat≤length.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length))) :
    source.clock-(evaluateHOLFiniteState source extensionScope).2.clock≤306 := by
  rw [extension_shapes.1]
  apply Input.ClockCost.declared_reached_current
  intro loaded _read checked
  cases loaded with
  | val payload=>
    cases payload with
    | word segment=>
      let current:=QueryBranch.bind source "seg" segment
      exact extension_length_cost current segment key level length bounded before installed (bind_lookup_same source "seg" segment)
        ((bind_lookup_other source "seg" "key" segment (by decide)).trans keyCell)
        ((bind_lookup_other source "seg" "level" segment (by decide)).trans levelCell)
        ((bind_lookup_other source "seg" "klen" segment (by decide)).trans lengthCell)
  | rStruct fields=>simp [shapeEqHOL,shapeOfHOLExact] at checked
  | nStruct name fields=>simp [shapeEqHOL,shapeOfHOLExact] at checked

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.extension_prefix_cost
#print axioms InitECandidate.Solver.Mpt.Insert.extension_length_cost
#print axioms InitECandidate.Solver.Mpt.Insert.extension_scope_cost
