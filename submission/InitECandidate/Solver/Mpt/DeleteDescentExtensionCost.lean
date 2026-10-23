import InitECandidate.Solver.Mpt.DeleteDescentExtensionEntry
import InitECandidate.Solver.Mpt.DeleteFrameProgram
import InitECandidate.Solver.Arenas.Cost
import InitECandidate.Solver.Input.ClockCostCurrentScoped

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Both allocator failure and the literal scratch stores/advance are
covered; only the real scratch allocation can spend source ticks. -/
theorem prefix_choice_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code prefixChoice 2 := by
  rw [prefix_choice_shape]
  have mismatch : Input.ClockCost.Bound code prefixMismatch 0:=Input.ClockCost.assign code _ _
  have push : Input.ClockCost.Bound code extensionFrameScope 2:=by
    rw [extension_shapes.2.2.2.2]
    exact Arenas.scoped_price code installed .down (ofString "fr") .one [.const 40#64] extensionPush 0
      (Input.ClockCost.of_quiet code _ (DeleteFrame.Kind.push_quiet .extension code))
  exact Input.ClockCost.conditional code _ _ _ 0 2 mismatch push

theorem extension_prefix_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length segment size : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property)
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (sizeCell : source.locals.lookup (ofString "sl")=some (.val (.word size))) :
    source.clock-(evaluateHOLFiniteState source prefixScope).2.clock≤min size.toNat (length.toNat-model.level.toNat)+4 := by
  have args:=extension_prefix_arguments source key length segment size limit nodeLower pathLower property model segmentCell sizeCell
  have number:=descent_remaining_number source key length limit nodeLower pathLower property model
  have small : min size.toNat (length-model.level).toNat≤64:=by
    have shorter:=Nat.min_le_right size.toNat (length-model.level).toNat
    have bounded:=model.bounded
    omega
  obtain ⟨callee,called,_aCell,leftCell,_bCell,rightCell⟩:=CommonPrefix.environment source.code.lookup segment size (key+model.level) (length-model.level)
    (CommonPrefix.original_code source.code model.pending.installed)
  have bodyPrice:=CommonPrefix.body_cost (callEntryStateHOLFinite source callee) size (length-model.level) small model.pending.installed leftCell rightCell
  have priced:=Input.ClockCost.scoped_current source (ofString "pl") .one (ofString "common_prefix_length") prefixArguments _ CommonPrefix.body prefixChoice callee .one
    (min size.toNat (length-model.level).toNat+1) 2 args called bodyPrice (prefix_choice_price source.code model.pending.installed)
  rw [prefix_scope_shape]
  rw [number] at priced
  omega

/-- All outcomes of the entire original extension case, bounded by the
shorter actual path/query plus4; arbitrarily long stored paths are allowed. -/
theorem extension_cost_current (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=2#64) :
    source.clock-(evaluateHOLFiniteState source extensionBlock).2.clock≤min (wordAt source.memory (model.node+40#64)).toNat (length.toNat-model.level.toNat)+4 := by
  have pointerRead:=(descent_path_reads source key length limit nodeLower pathLower property model active (Or.inr tag)).1
  let segment:=wordAt source.memory (model.node+32#64)
  let size:=wordAt source.memory (model.node+40#64)
  let segmented:=QueryBranch.bind source "seg" segment
  let segmentModel:=model.bind_auxiliary source key length limit nodeLower pathLower property "seg" segment (by decide)
  have sizeRead:=(descent_path_reads segmented key length limit nodeLower pathLower property segmentModel active (Or.inr tag)).2
  let sized:=QueryBranch.bind segmented "sl" size
  let sizedModel:=segmentModel.bind_auxiliary segmented key length limit nodeLower pathLower property "sl" size (by decide)
  have segmentCell : sized.locals.lookup (ofString "seg")=some (.val (.word segment)):=
    (bind_lookup_other segmented "sl" "seg" size (by decide)).trans (bind_lookup_same _ _ _)
  have sizeCell : sized.locals.lookup (ofString "sl")=some (.val (.word size)):=bind_lookup_same _ _ _
  have price:=extension_prefix_cost sized key length segment size limit nodeLower pathLower property sizedModel segmentCell sizeCell
  rw [extension_shapes.1]
  apply Input.ClockCost.declared_current source "seg" (field "node" 32#64) segment afterSegment _ pointerRead
  rw [extension_shapes.2.1]
  exact Input.ClockCost.declared_current segmented "sl" (field "node" 40#64) size prefixScope _ sizeRead price

theorem extension_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=2#64) :
    source.clock-(evaluateHOLFiniteState source extensionBlock).2.clock≤68 := by
  have price:=extension_cost_current source key length limit nodeLower pathLower property model active tag
  have shorter:=Nat.min_le_right (wordAt source.memory (model.node+40#64)).toNat (length.toNat-model.level.toNat)
  have bounded:=model.bounded
  omega

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.prefix_choice_price
#print axioms InitECandidate.Solver.Mpt.DeleteBody.extension_prefix_cost
#print axioms InitECandidate.Solver.Mpt.DeleteBody.extension_cost_current
#print axioms InitECandidate.Solver.Mpt.DeleteBody.extension_cost
