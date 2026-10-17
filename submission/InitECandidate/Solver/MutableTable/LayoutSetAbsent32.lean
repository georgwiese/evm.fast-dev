import InitECandidate.Solver.MutableTable.LayoutUpdate32

namespace InitECandidate.Solver.MutableTable.Layout32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
attribute [local instance] Classical.propDecidable

/-- Actual missing-key setter suffix: the preallocated immutable table does
not grow, and the real raw-insertion call extends its physical/logical build. -/
theorem absent_set (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (keyPointer : BitVec 64) (count : Nat) (input : List (Find.Key32×BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (bits : Nat) (small : bits<64) (power : plan.capacity=2^bits)
    (built : Built bits source plan keyPointer count input logical) (processed : input.length≤plan.count)
    (key : Find.Key32) (value : BitVec 64) (absent : lastValue key input=none) (words : Fin 4→BitVec 64)
    (tLocal : source.locals.lookup (ofString "t")=some (.val (.word (BitVec.ofNat 64 plan.table))))
    (keyLocal : source.locals.lookup (ofString "key")=some (.val (.word keyPointer)))
    (valueLocal : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (iLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (aligned : keyPointer.toNat%8=0) (before : keyPointer.toNat+32≤plan.table) (little : source.be=false)
    (view : MemoryBytes.WordView source keyPointer words) (bytes : MemoryBytes.ByteView source keyPointer key)
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (copyCode : source.code.lookup (ofString "memcpy")=some (Copy32.formals,Copy32.body,.one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw")=some (TableCall.formals,Insert.body,.one))
    (enough : input.length+4≤source.clock) :
    ∃ index paid,index<plan.capacity ∧ paid≤input.length+4 ∧
      evaluateHOLFiniteState source Set.afterIndex=(some (.returned (.val (.word 0#64))),
        emptyLocalsHOLFinite {source with memory:=resultMemory source.memory plan keyPointer index count value words,clock:=source.clock-paid}) ∧
      Built bits (emptyLocalsHOLFinite {source with memory:=resultMemory source.memory plan keyPointer index count value words,clock:=source.clock-paid})
        plan keyPointer (count+1) (input++[(key,value)]) (Placement.put logical index key value) := by
  have room:=ready.room
  have fits:=ready.fits
  have headerMapped (offset : Nat) (inside : offset<72) (aligned : offset%8=0) :
      source.memaddrs (BitVec.ofNat 64 plan.table+BitVec.ofNat 64 offset) := by
    rw [header_cell plan offset];exact word_mapped source plan ready domain .header offset inside aligned
  have capRead:=Find.table_read source (BitVec.ofNat 64 plan.table) 16#64 (BitVec.ofNat 64 plan.capacity) tLocal
    (headerMapped 16 (by decide) (by decide)) built.header.find.capacity
  have skipped : evaluateHOLFiniteState source (.ite Set.presentTest Set.updateBranch .skip)=(none,source) := by
    simp only [eval] at capRead
    simp [evaluateHOLFiniteState_ite,Set.presentTest,localVar,evalHOLExact,toExact,iLocal,capRead,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have noGrowth:=Set.no_growth source (BitVec.ofNat 64 plan.table) count plan.capacity plan.count
    (by have:=built.countBound;omega) ready.room (by omega) tLocal
    (by intro offset member;simp only [List.mem_cons,List.not_mem_nil,or_false] at member;rcases member with rfl|rfl <;> exact headerMapped _ (by decide) (by decide))
    built.header.find.capacity built.header.count
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address))
      [localVar "t",localVar "key",localVar "value"]=some (TableCall.values (BitVec.ofNat 64 plan.table) keyPointer value) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,TableCall.values,tLocal,keyLocal,valueLocal]
  obtain ⟨index,paid,inside,bound,callRun,next⟩:=insert_build_call source plan ready domain keyPointer count input logical bits small power built
    (by omega) key value absent words aligned before little view bytes hashCode copyCode insertCode _ args enough
  let post:={source with memory:=resultMemory source.memory plan keyPointer index count value words,clock:=source.clock-paid}
  change evaluateHOLFiniteState source Set.insertCall=(none,post) at callRun
  refine ⟨index,paid,inside,bound,?_,built_fields post (emptyLocalsHOLFinite post) plan bits keyPointer (count+1) _ _ rfl rfl rfl next⟩
  rw [Set.afterIndex,StateSteps.next_sequence source source _ _ skipped (Nat.le_refl _),
    Set.afterPresent,StateSteps.next_sequence source source _ _ noGrowth (Nat.le_refl _),
    StateSteps.next_sequence source post _ _ callRun (Nat.sub_le _ _)]
  simp [Insert.returnZero,evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  rfl

end InitECandidate.Solver.MutableTable.Layout32

#print axioms InitECandidate.Solver.MutableTable.Layout32.absent_set
