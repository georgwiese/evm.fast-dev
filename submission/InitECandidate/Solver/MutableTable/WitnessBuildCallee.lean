import InitECandidate.Solver.MutableTable.WitnessBuildInputs

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- For the empty sentinel, the table itself is a harmless ghost record
frontier; the actual program never reads a record in that branch. -/
def effectiveRecords (array heap : BitVec 64) (count : Nat) := if count=0 then heap.toNat else array.toNat

def bodyPrice (slices : Nat→Graph.Slice) (count : Nat) := wholeVariablePrice slices count+1

/-- Derived actual output data and protected preceding memory. Capacity,
heap growth and arbitrary-collision history come from the original program. -/
structure Normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap : BitVec 64) (count : Nat)
    (stp pad scratch : BitVec 64) : Prop where
  table : ∃ bits nextCount input logical,
    let plan:=Constructor.allocationPlan (effectiveRecords array heap count) heap.toNat count (2^bits)
    2≤bits ∧ bits≤32 ∧ 2^bits≤4*count+4 ∧ Layout32.Built bits target plan scratch nextCount input logical ∧ History plan input ∧ input.length=count
  control : ∃ next,heap.toNat≤next ∧ next≤heap.toNat+72+57*(4*count+4)+7 ∧ next%8=0 ∧
    KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl {source with globals:=source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 next)))}
  memory : ∀ query,Keccak256.Protected stp pad scratch query→query.toNat<heap.toNat→target.memory query=source.memory query

theorem callee_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64) (actual : Inputs source array heap count maximum slices stp pad scratch)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (arrayCell : callee.lookup (ofString "slice_arr")=some (.val (.word array)))
    (countCell : callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))) :
    (callEntryStateHOLFinite source callee).clock-(evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).2.clock≤bodyPrice slices count := by
  let entry:=callEntryStateHOLFinite source callee
  rcases actual.callee source array heap count maximum slices stp pad scratch callee arrayCell countCell with empty|ready
  · obtain ⟨zero,ready⟩ := empty
    have price:=empty_body_cost entry (evaluateHOLFiniteState entry body).2 heap.toNat scratch ready (evaluateHOLFiniteState entry body).1 rfl
    simpa only [bodyPrice,zero,wholeVariablePrice,recordBudget,Nat.mul_zero,Nat.zero_add,Nat.add_zero] using price
  · obtain ⟨nonempty,ready⟩ := ready
    exact (body_cost entry (evaluateHOLFiniteState entry body).2 array.toNat heap.toNat count maximum slices stp pad scratch ready _ rfl).trans (Nat.le_add_right _ _)

/-- A real returned constructor derives its table and frame for both the
empty and nonempty branches, at the actual current caller heap. -/
theorem callee_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64) (actual : Inputs source array heap count maximum slices stp pad scratch)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (arrayCell : callee.lookup (ofString "slice_arr")=some (.val (.word array)))
    (countCell : callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned value),target)) :
    value=.val (.word heap) ∧ Normal source target array heap count stp pad scratch := by
  let entry:=callEntryStateHOLFinite source callee
  rcases actual.callee source array heap count maximum slices stp pad scratch callee arrayCell countCell with empty|ready
  · obtain ⟨zero,ready⟩ := empty
    obtain ⟨valueEq,built,ffi,globals,memory,forward,cost,control⟩ := empty_normal_any_clock entry target heap.toNat scratch ready value normal
    refine ⟨by simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using valueEq,?_,?_,?_⟩
    · refine ⟨2,0,[],fun _=>none,by decide,by decide,?_,?_,.empty,?_⟩
      · rw [zero]; decide
      · simpa [effectiveRecords,zero] using built
      · simp [zero]
    · exact ⟨heap.toNat+304,by omega,by rw [zero]; omega,by have h:=actual.heapAligned; omega,control⟩
    · intro query kept earlier
      exact memory query earlier
  · obtain ⟨nonempty,ready⟩ := ready
    obtain ⟨valueEq,bits,nextCount,input,logical,lower,upper,built,history,length,rows,control,forward,cost,capacity,memory⟩ :=
      normal_any_clock entry target array.toNat heap.toNat count maximum slices stp pad scratch ready value normal
    refine ⟨by simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using valueEq,?_,?_,memory⟩
    · exact ⟨bits,nextCount,input,logical,lower,upper,capacity,by simpa only [effectiveRecords,if_neg nonempty] using built,by simpa only [effectiveRecords,if_neg nonempty] using history,length⟩
    · let next:=heap.toNat+72+57*(2^bits)+Constructor.padding (2^bits)
      have padding:=Constructor.padding_bound (2^bits)
      have aligned : next%8=0 := by
        have heapAligned:=actual.heapAligned
        rcases Capacity.power_shape bits lower with four|multiple
        · simp [next,Constructor.padding,four,Nat.add_mod,heapAligned]
        · by_cases four : 2^bits=4
          · simp [next,Constructor.padding,four,Nat.add_mod,heapAligned]
          · simp [next,Constructor.padding,four,Nat.add_mod,Nat.mul_mod,multiple,heapAligned]
      exact ⟨next,by dsimp [next]; omega,by dsimp [next]; omega,aligned,control⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.callee_cost
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.callee_normal
