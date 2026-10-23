import InitECandidate.Solver.Mpt.DeleteDescentExtensionEntry
import InitECandidate.Solver.Mpt.DeleteDescentExtensionMismatch
import InitECandidate.Solver.Mpt.DeleteDescentExtensionMatched
import InitECandidate.Solver.Mpt.DeleteDescentOutputClock

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Join the real prefix comparison with its two actual continuations.
A mismatch stops at the registered current node; a genuine full match
allocates the saved parent and strictly advances within the key. -/
theorem extension_prefix_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length segment size : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=2#64) (stopped : model.go=0#64)
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (sizeCell : source.locals.lookup (ofString "sl")=some (.val (.word size)))
    (segmentEq : wordAt source.memory (model.node+32#64)=segment)
    (sizeEq : wordAt source.memory (model.node+40#64)=size)
    (normal : evaluateHOLFiniteState source prefixScope=(none,target)) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  obtain ⟨word,clock,inner,bound,_price,_forward,continued,endpoint⟩:=extension_prefix_entry source target key length segment size limit nodeLower pathLower property model segmentCell sizeCell normal
  let paidState:={source with clock:=clock}
  let paidModel:=model.with_clock source key length limit nodeLower pathLower property clock
  let current:=QueryBranch.bind paidState "pl" word
  let ready:=paidModel.bind_auxiliary paidState key length limit nodeLower pathLower property "pl" word (by decide)
  have wordCell : current.locals.lookup (ofString "pl")=some (.val (.word word)):=bind_lookup_same _ _ _
  have currentSize : current.locals.lookup (ofString "sl")=some (.val (.word size)):=
    (bind_lookup_other paidState "pl" "sl" word (by decide)).trans sizeCell
  have output : Nonempty (DescentOutput current inner key length limit nodeLower pathLower property ready):=by
    by_cases smaller : word.toNat<size.toNat
    · exact prefix_mismatch_output current inner key length limit nodeLower pathLower property ready word size wordCell currentSize smaller stopped continued
    · have matched:=(prefix_matched_numbers word size (length.toNat-model.level.toNat) bound smaller).2
      rw [prefix_dispatch current word size wordCell currentSize,if_neg smaller] at continued
      have currentSegment : current.locals.lookup (ofString "seg")=some (.val (.word segment)):=
        (bind_lookup_other paidState "pl" "seg" word (by decide)).trans segmentCell
      exact extension_matched_output current inner key length segment size limit nodeLower pathLower property ready active tag currentSegment currentSize segmentEq sizeEq matched continued
  obtain ⟨output⟩:=output
  obtain ⟨exited⟩:=DescentOutput.restore_auxiliary paidState inner key length limit nodeLower pathLower property paidModel "pl" word (by decide) output
  rw [endpoint]
  exact DescentOutput.of_clock source (restore source "pl" inner) key length limit nodeLower pathLower property model clock exited

/-- Whole unchanged extension descent case: the real mapped seg/sl
declarations, bounded comparison, actual stop or scratch push, and both
lexical exits preserve the complete current descent invariant. -/
theorem extension_output_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=2#64) (stopped : model.go=0#64)
    (normal : evaluateHOLFiniteState source extensionBlock=(none,target)) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  let segment:=wordAt source.memory (model.node+32#64)
  let size:=wordAt source.memory (model.node+40#64)
  let segmented:=QueryBranch.bind source "seg" segment
  let segmentModel:=model.bind_auxiliary source key length limit nodeLower pathLower property "seg" segment (by decide)
  let sized:=QueryBranch.bind segmented "sl" size
  let sizeModel:=segmentModel.bind_auxiliary segmented key length limit nodeLower pathLower property "sl" size (by decide)
  obtain ⟨inner,continued,endpoint⟩:=extension_fields_entry source target key length limit nodeLower pathLower property model active tag normal
  have segmentCell : sized.locals.lookup (ofString "seg")=some (.val (.word segment)):=
    (bind_lookup_other segmented "sl" "seg" size (by decide)).trans (bind_lookup_same source "seg" segment)
  have sizeCell : sized.locals.lookup (ofString "sl")=some (.val (.word size)):=bind_lookup_same _ _ _
  obtain ⟨output⟩:=extension_prefix_output sized inner key length segment size limit nodeLower pathLower property sizeModel active tag stopped segmentCell sizeCell rfl rfl continued
  obtain ⟨exitedSize⟩:=DescentOutput.restore_auxiliary segmented inner key length limit nodeLower pathLower property segmentModel "sl" size (by decide) output
  rw [endpoint]
  exact DescentOutput.restore_auxiliary source (restore segmented "sl" inner) key length limit nodeLower pathLower property model "seg" segment (by decide) exitedSize

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.extension_prefix_output
#print axioms InitECandidate.Solver.Mpt.DeleteBody.extension_output_normal
