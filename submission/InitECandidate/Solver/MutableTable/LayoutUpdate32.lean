import InitECandidate.Solver.MutableTable.InsertBuildCall32
import InitECandidate.Solver.MutableTable.SetUpdate

namespace InitECandidate.Solver.MutableTable.Layout32
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
attribute [local instance] Classical.propDecidable

def updateMemory (memory : WordWrites.Memory) (plan : AllocatedLayout.Plan) (index : Nat) (value : BitVec 64) : WordWrites.Memory:=
  StoreWord.put memory (BitVec.ofNat 64 (base plan .values)+BitVec.ofNat 64 index*8#64) value

theorem update_header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (key : BitVec 64) (index count : Nat) (inside : index<plan.capacity)
    (value : BitVec 64) (header : Header source plan key count) :
    Header {source with memory:=updateMemory source.memory plan index value} plan key count := by
  have fixed (offset : Nat) (insideHeader : offset<72) :
      updateMemory source.memory plan index value (BitVec.ofNat 64 plan.table+BitVec.ofNat 64 offset)=
        source.memory (BitVec.ofNat 64 plan.table+BitVec.ofNat 64 offset) := by
    apply if_neg
    rw [header_cell plan offset,value_cell]
    exact separate plan ready .header .values (by decide) _ _ insideHeader (by change _<8*plan.capacity;omega)
  refine ⟨⟨header.find.mapped,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  · exact (fixed 16 (by decide)).trans header.find.capacity
  · simpa only [BitVec.add_zero] using (fixed 0 (by decide)).trans
      (show source.memory (BitVec.ofNat 64 plan.table+0#64)=.word (parameters plan key).keyLength by simpa using header.find.keyLength)
  · exact (fixed 8 (by decide)).trans header.find.stride
  · exact (fixed 32 (by decide)).trans header.find.keys
  · exact (fixed 48 (by decide)).trans header.find.used
  · exact (fixed 40 (by decide)).trans header.values
  · exact (fixed 56 (by decide)).trans header.order
  · exact (fixed 64 (by decide)).trans header.position
  · exact (fixed 24 (by decide)).trans header.count

/-- The real existing-key setter suffix extends the build history while
preserving the natural count and every other represented slot. -/
theorem update_build (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (bits : Nat) (keyPointer : BitVec 64) (count : Nat) (input : List (Find.Key32×BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (built : Built bits source plan keyPointer count input logical)
    (index : Nat) (inside : index<plan.capacity) (key : Find.Key32) (old value : BitVec 64)
    (stored : logical index=some (key,old))
    (tLocal : source.locals.lookup (ofString "t")=some (.val (.word (BitVec.ofNat 64 plan.table))))
    (iLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (valueLocal : source.locals.lookup (ofString "value")=some (.val (.word value))) :
    evaluateHOLFiniteState source Set.afterIndex=(some (.returned (.val (.word 0#64))),
      emptyLocalsHOLFinite {source with memory:=updateMemory source.memory plan index value}) ∧
    Built bits (emptyLocalsHOLFinite {source with memory:=updateMemory source.memory plan index value}) plan keyPointer count
      (input++[(key,value)]) (Placement.put logical index key value) := by
  classical
  have fits:=ready.fits
  have capSmall : plan.capacity<2^64:=by omega
  have distinct : BitVec.ofNat 64 index≠BitVec.ofNat 64 plan.capacity := by
    intro equal
    have numbers:=congrArg BitVec.toNat equal
    rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt capSmall] at numbers
    omega
  have headerMapped (offset : Nat) (inside : offset<72) (aligned : offset%8=0) :
      source.memaddrs (BitVec.ofNat 64 plan.table+BitVec.ofNat 64 offset) := by
    rw [header_cell plan offset];exact word_mapped source plan ready domain .header offset inside aligned
  have valueMapped : source.memaddrs (BitVec.ofNat 64 (base plan .values)+BitVec.ofNat 64 index*8#64) := by
    rw [value_cell];exact word_mapped source plan ready domain .values _ (by change _<8*plan.capacity;omega) (by omega)
  have run:=Set.update_execute source (BitVec.ofNat 64 plan.table) (BitVec.ofNat 64 (base plan .values)) (BitVec.ofNat 64 index)
    (BitVec.ofNat 64 plan.capacity) value tLocal iLocal valueLocal (headerMapped 16 (by decide) (by decide)) built.header.find.capacity
    (headerMapped 40 (by decide) (by decide)) built.header.values valueMapped distinct
  have keys:=Find.value_store_keys source (parameters plan keyPointer) plan.capacity index logical built.keys key old value stored
    (BitVec.ofNat 64 (base plan .values)+BitVec.ofNat 64 index*8#64)
    (by
      intro i inside
      rw [used_byte_cell plan ready keyPointer i inside,value_cell]
      exact separate plan ready .used .values (by decide) _ _ (by change _<plan.capacity;omega) (by change _<8*plan.capacity;omega))
    (by
      intro i inside byte
      rw [key_byte_cell plan ready keyPointer i byte.val inside byte.isLt,value_cell]
      exact separate plan ready .keys .values (by decide) _ _ (by change _<32*plan.capacity;have:=byte.isLt;omega)
        (by change _<8*plan.capacity;omega))
  have values:=Find.value_store_model source _ plan.capacity index inside logical built.values key value valueMapped (values_fit plan ready)
  have header:=update_header source plan ready keyPointer index count inside value built.header
  have invariants:=Placement.build_invariants plan.capacity (Find.hashHome bits) input logical built.trace
  have trace : Placement.Builds plan.capacity (Find.hashHome bits) (input++[(key,value)]) (Placement.put logical index key value):=
    .snoc input logical built.trace index key value inside (Or.inr ⟨old,stored⟩)
      (by intro q qBound v cell;exact invariants.2.2 q qBound index inside key v old cell stored)
      (invariants.1 index inside key old stored)
  let changed:={source with memory:=updateMemory source.memory plan index value}
  have next : Built bits changed plan keyPointer count (input++[(key,value)]) (Placement.put logical index key value):=
    ⟨header,keys,values,trace,by have:=built.countBound;simp only [List.length_append,List.length_singleton];omega⟩
  exact ⟨run,built_fields changed (emptyLocalsHOLFinite changed) plan bits keyPointer count _ _ rfl rfl rfl next⟩

end InitECandidate.Solver.MutableTable.Layout32

#print axioms InitECandidate.Solver.MutableTable.Layout32.update_header
#print axioms InitECandidate.Solver.MutableTable.Layout32.update_build
