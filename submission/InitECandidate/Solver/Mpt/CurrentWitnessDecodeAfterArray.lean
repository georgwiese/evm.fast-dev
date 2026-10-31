import InitECandidate.Solver.Mpt.CurrentWitnessDecodePairCost
import InitECandidate.Solver.Mpt.CurrentWitnessDecodeZero
import InitECandidate.Solver.Mpt.WitnessDecodeRecursiveCost
import InitECandidate.Solver.Input.NoFallthroughEnds
import InitECandidate.Solver.Input.SequenceChoice

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem after_array_shape : afterArray=
    .seq (.ite (.cmp .equal (field "sl" 1) (.const 2#64)) pairBody .skip) branchBody := by
  unfold afterArray
  rw [after_slices_shape]
  rfl

set_option maxRecDepth 100000 in
theorem current_pair_no_fallthrough : NoFallthrough pairBody :=
  NoFallthrough.of_ends_in_return pairBody (by
    simp only [pairBody,afterArray,afterSlices,slicesCall,WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,
      seqRest,seqFirst,decRest,callRest,yesBranch,Guest.Software.guestFn__decode_step,
      progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,endsInReturn])

theorem after_array_select (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array count : BitVec 64)
    (sliceCell : source.locals.lookup (ofString "sl")=some (Rlp.Slices.result array count)) :
    evaluateHOLFiniteState source afterArray=
      if count=2#64 then evaluateHOLFiniteState source pairBody else evaluateHOLFiniteState source branchBody := by
  have selected : evaluateHOLFiniteState source (.ite (.cmp .equal (field "sl" 1) (.const 2#64)) pairBody .skip)=
      if count=2#64 then evaluateHOLFiniteState source pairBody else (none,source) := by
    by_cases two : count=2#64
    · simp [evaluateHOLFiniteState_ite,field,localVar,evalHOLExact,toExact,sliceCell,Rlp.Slices.result,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,two]
    · simp [evaluateHOLFiniteState_ite,field,localVar,evalHOLExact,toExact,sliceCell,Rlp.Slices.result,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,two,evaluateHOLFiniteState_skip]
  rw [after_array_shape]
  exact sequence_choice source _ pairBody branchBody (count=2#64) selected current_pair_no_fallthrough

theorem two_items (items : List Rlp.ListItem) (length : items.length=2) : ∃ first second,items=[first,second] := by
  cases items with
  | nil=>simp at length
  | cons first rest=>
    cases rest with
    | nil=>simp at length
    | cons second rest=>
      cases rest with
      | nil=>exact ⟨first,second,rfl⟩
      | cons third rest=>simp only [List.length_cons] at length; omega

/-- The actual slice count selects its genuine two-row path or the bounded
branch constructor. The two-item body cannot fall through into that branch. -/
theorem current_after_array_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer heap count : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (countEq : count.toNat=items.length)
    (sliceCell : source.locals.lookup (ofString "sl")=some (Rlp.Slices.result array count))
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (small : bytes≤1024) (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : Rlp.LiveArena source) :
    source.clock-(evaluateHOLFiniteState source afterArray).2.clock≤bytes/4+120*bytes+266 := by
  rw [after_array_select source array count sliceCell]
  by_cases two : count=2#64
  · rw [if_pos two]
    have length : items.length=2 := by rw [←countEq,two]; rfl
    obtain ⟨first,second,rfl⟩:=two_items items length
    exact Nat.le_trans (current_pair_price source array pointer heap bytes [first,second] first second rows rfl rfl arrayCell small beforeArray heapCell heapArena heapBound aligned arena) (by omega)
  · rw [if_neg two]
    exact Nat.le_trans (branch_body_cost source arena) (by omega)

/-- The selected actual body returns either a terminal node or a pending
frame. This tag fact needs no assumed future parse or allocation success. -/
theorem current_after_array_binary (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    ReturnFacts.Returns source afterArray BinaryResult := by
  rw [after_array_shape]
  apply ReturnFacts.sequence
  · exact ReturnFacts.conditional source _ _ _ BinaryResult
      (current_pair_binary source) (ReturnFacts.skip source BinaryResult)
  · intro middle normal
    exact branch_body_binary middle

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_after_array_price
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_after_array_binary
