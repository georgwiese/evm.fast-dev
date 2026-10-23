import InitECandidate.Solver.Mpt.DeleteDescentPathReads
import InitECandidate.Solver.Mpt.DeleteDescentExtensionProgram
import InitECandidate.Solver.Mpt.CommonPrefixNone
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Both original declarations read the real registered extension fields
before entering its actual common-prefix call and lexical exits. -/
theorem extension_fields_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=2#64)
    (normal : evaluateHOLFiniteState source extensionBlock=(none,target)) :
    let segment:=wordAt source.memory (model.node+32#64)
    let size:=wordAt source.memory (model.node+40#64)
    let segmented:=QueryBranch.bind source "seg" segment
    ∃ inner,evaluateHOLFiniteState (QueryBranch.bind segmented "sl" size) prefixScope=(none,inner) ∧
      target=restore source "seg" (restore segmented "sl" inner) := by
  have pointerRead:=(descent_path_reads source key length limit nodeLower pathLower property model active (Or.inr tag)).1
  rw [extension_shapes.1] at normal
  obtain ⟨segmentInner,continued,endpoint⟩:=Input.declaration_none_word source target "seg" (field "node" 32#64) _ afterSegment pointerRead normal
  let segmented:=QueryBranch.bind source "seg" (wordAt source.memory (model.node+32#64))
  let segmentModel:=model.bind_auxiliary source key length limit nodeLower pathLower property "seg" (wordAt source.memory (model.node+32#64)) (by decide)
  have sizeRead:=(descent_path_reads segmented key length limit nodeLower pathLower property segmentModel active (Or.inr tag)).2
  rw [extension_shapes.2.1] at continued
  obtain ⟨inner,run,segmentEndpoint⟩:=Input.declaration_none_word segmented segmentInner "sl" (field "node" 40#64) _ prefixScope sizeRead continued
  exact ⟨inner,run,endpoint.trans (congrArg (restore source "seg") segmentEndpoint)⟩

theorem extension_prefix_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length segment size : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property)
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (sizeCell : source.locals.lookup (ofString "sl")=some (.val (.word size))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) prefixArguments=
      some (CommonPrefix.values segment size (key+model.level) (length-model.level)) := by
  obtain ⟨suffixRead,remainingRead⟩:=descent_query_reads source key length limit nodeLower pathLower property model
  simp only [eval] at suffixRead remainingRead
  simp only [prefixArguments,CommonPrefix.values,evalListHOLFinite,evalListHOLExact,suffixRead,remainingRead]
  simp [localVar,evalHOLExact,toExact,segmentCell,sizeCell]

/-- Actual prefix execution supplies its real bounded word and pure
caller continuation. The bound is the shorter stored path/query suffix. -/
theorem extension_prefix_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length segment size : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property)
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (sizeCell : source.locals.lookup (ofString "sl")=some (.val (.word size)))
    (normal : evaluateHOLFiniteState source prefixScope=(none,target)) :
    ∃ word clock inner,word.toNat≤min size.toNat (length.toNat-model.level.toNat) ∧
      source.clock-clock≤min size.toNat (length.toNat-model.level.toNat)+2 ∧ clock≤source.clock ∧
      evaluateHOLFiniteState (QueryBranch.bind {source with clock:=clock} "pl" word) prefixChoice=(none,inner) ∧ target=restore source "pl" inner := by
  have args:=extension_prefix_arguments source key length segment size limit nodeLower pathLower property model segmentCell sizeCell
  have number:=descent_remaining_number source key length limit nodeLower pathLower property model
  have small : min size.toNat (length-model.level).toNat≤64:=by
    have shorter:=Nat.min_le_right size.toNat (length-model.level).toNat
    have bounded:=model.bounded
    omega
  rw [prefix_scope_shape] at normal
  obtain ⟨word,clock,inner,bound,price,forward,continued,endpoint⟩:=CommonPrefix.none_prefix source target "pl" prefixArguments prefixChoice segment size (key+model.level) (length-model.level)
    small model.pending.installed args normal
  exact ⟨word,clock,inner,(by simpa only [number] using bound),(by simpa only [number] using price),forward,continued,endpoint⟩

/-- A reached non-smaller prefix must equal the stored segment length,
and that segment fits within the actual remaining query. -/
theorem prefix_matched_numbers (prefixLength segmentLength : BitVec 64) (remaining : Nat)
    (bound : prefixLength.toNat≤min segmentLength.toNat remaining) (notSmaller : ¬prefixLength.toNat<segmentLength.toNat) :
    prefixLength=segmentLength ∧ segmentLength.toNat≤remaining := by
  have left:=bound.trans (Nat.min_le_left _ _)
  have right:=bound.trans (Nat.min_le_right _ _)
  exact ⟨BitVec.eq_of_toNat_eq (by omega),by omega⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.extension_fields_entry
#print axioms InitECandidate.Solver.Mpt.DeleteBody.extension_prefix_arguments
#print axioms InitECandidate.Solver.Mpt.DeleteBody.extension_prefix_entry
#print axioms InitECandidate.Solver.Mpt.DeleteBody.prefix_matched_numbers
