import InitECandidate.Solver.MutableTable.LayoutSetAbsent32
import InitECandidate.Solver.MutableTable.FindDictionaryCall32

namespace InitECandidate.Solver.MutableTable.Layout32
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
attribute [local instance] Classical.propDecidable

/-- Complete original immutable-table setter, including duplicate updates,
actual find and raw-insert calls. It extends last-record-wins build history
without growth, paying at most7*processed+6 source clocks. -/
theorem set_build (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (keyPointer : BitVec 64) (count : Nat) (input : List (Find.Key32×BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (bits : Nat) (small : bits<64) (power : plan.capacity=2^bits)
    (built : Built bits source plan keyPointer count input logical) (processed : input.length≤plan.count)
    (key : Find.Key32) (value : BitVec 64) (words : Fin 4→BitVec 64)
    (tLocal : source.locals.lookup (ofString "t")=some (.val (.word (BitVec.ofNat 64 plan.table))))
    (keyLocal : source.locals.lookup (ofString "key")=some (.val (.word keyPointer)))
    (valueLocal : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (aligned : keyPointer.toNat%8=0) (before : keyPointer.toNat+32≤plan.table) (little : source.be=false)
    (view : MemoryBytes.WordView source keyPointer words) (bytes : MemoryBytes.ByteView source keyPointer key)
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (copyCode : source.code.lookup (ofString "memcpy")=some (Copy32.formals,Copy32.body,.one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw")=some (TableCall.formals,Insert.body,.one))
    (memeqCode : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (findCode : source.code.lookup (ofString "htab_find_slot")=some (Find.formals,Find.body,.one))
    (enough : 7*input.length+6≤source.clock) :
    ∃ index nextCount paid memory target,index<plan.capacity ∧ count≤nextCount ∧ nextCount≤count+1 ∧ paid≤7*input.length+6 ∧
      evaluateHOLFiniteState source Set.body=(some (.returned (.val (.word 0#64))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=memory,clock:=source.clock-paid} ∧
      Built bits target plan keyPointer nextCount (input++[(key,value)]) (Placement.put logical index key value) ∧
      ((memory=updateMemory source.memory plan index value ∧ nextCount=count) ∨
        (memory=resultMemory source.memory plan keyPointer index count value words ∧ nextCount=count+1)) := by
  classical
  let p:=parameters plan keyPointer
  let dictionary:=fun query=>lastValue query input
  have invariants:=Placement.build_invariants plan.capacity (Find.hashHome bits) input logical built.trace
  obtain ⟨order,lengthBound,covered⟩:=Placement.build_cover plan.capacity (Find.hashHome bits) input logical built.trace
  have room:=ready.room
  have fits:=ready.fits
  have capacity : p.capacity=BitVec.ofNat 64 (2^bits):=by simp [p,parameters,TableEmpty.parameters,power]
  have cells:=Find.HeaderData.with_locals source source (BitVec.ofNat 64 plan.table) p built.header.find rfl rfl tLocal keyLocal
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "t",localVar "key"]=
      some [.val (.word (BitVec.ofNat 64 plan.table)),.val (.word keyPointer)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,tLocal,keyLocal]
  obtain ⟨findPaid,slot,paidBound,spec,findCall⟩:=Find.dictionary32_call source (BitVec.ofNat 64 plan.table) p cells rfl bits small capacity logical
    (by simpa only [← power] using built.keys) dictionary (by simpa only [← power] using invariants.2.1)
    (by simpa only [← power] using invariants.1) order (by omega) (by simpa only [← power] using covered)
    (by intro i inside;exact key_fits plan ready keyPointer i (by rw [power];exact inside))
    key bytes (by change keyPointer.toNat+32<2^64;omega) little hashCode memeqCode findCode "i" [localVar "t",localVar "key"] Set.afterIndex args (by omega)
  let entered:=bind {source with clock:=source.clock-findPaid} "i" slot
  have caller : evaluateHOLFiniteState source Set.body=
      (let output:=evaluateHOLFiniteState entered Set.afterIndex;(output.1,restore source "i" output.2)) := by
    rw [Set.body_shape]
    exact findCall
  have enteredBuilt:=built_fields source entered plan bits keyPointer count input logical rfl rfl rfl built
  have enteredT : entered.locals.lookup (ofString "t")=some (.val (.word (BitVec.ofNat 64 plan.table))):=
    (bind_lookup_other _ "i" "t" _ (by decide)).trans tLocal
  have enteredKey : entered.locals.lookup (ofString "key")=some (.val (.word keyPointer)):=
    (bind_lookup_other _ "i" "key" _ (by decide)).trans keyLocal
  have enteredValue : entered.locals.lookup (ofString "value")=some (.val (.word value)):=
    (bind_lookup_other _ "i" "value" _ (by decide)).trans valueLocal
  have enteredI : entered.locals.lookup (ofString "i")=some (.val (.word slot)):=bind_lookup_same _ _ _
  rcases spec with ⟨same,missing⟩|⟨index,old,inside,indexNat,stored,present⟩
  · change lastValue key input=none at missing
    have capI : entered.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 plan.capacity))) := by
      rw [same] at enteredI
      exact enteredI
    obtain ⟨index,paid,indexInside,bound,tailRun,next⟩:=absent_set entered plan ready domain keyPointer count input logical bits small power enteredBuilt processed
      key value missing words enteredT enteredKey enteredValue capI aligned before little
      (word_view_fields source entered keyPointer words rfl rfl view) (MemoryBytes.byteView_of_fields source entered rfl rfl rfl keyPointer key bytes)
      hashCode copyCode insertCode (by change input.length+4≤source.clock-findPaid;omega)
    let memory:=resultMemory source.memory plan keyPointer index count value words
    let post:=emptyLocalsHOLFinite {entered with memory:=memory,clock:=entered.clock-paid}
    let target:=restore source "i" post
    refine ⟨index,count+1,findPaid+paid,memory,target,indexInside,by omega,Nat.le_refl _,by omega,?_,?_,?_,Or.inr ⟨rfl,rfl⟩⟩
    · rw [caller,tailRun]
      rfl
    · change emptyLocalsHOLFinite {source with memory:=memory,clock:=source.clock-findPaid-paid}=_
      have subtract : source.clock-findPaid-paid=source.clock-(findPaid+paid):=by omega
      rw [subtract]
    · exact built_fields post target plan bits keyPointer (count+1) _ _ rfl rfl rfl next
  · have indexInside : index<plan.capacity:=by rw [power];exact inside
    have wordEq : slot=BitVec.ofNat 64 index := by
      apply BitVec.eq_of_toNat_eq
      rw [indexNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have indexI : entered.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) := by
      rw [wordEq] at enteredI
      exact enteredI
    obtain ⟨tailRun,next⟩:=update_build entered plan ready domain bits keyPointer count input logical enteredBuilt index indexInside key old value stored enteredT indexI enteredValue
    let memory:=updateMemory source.memory plan index value
    let post:=emptyLocalsHOLFinite {entered with memory:=memory}
    let target:=restore source "i" post
    refine ⟨index,count,findPaid,memory,target,indexInside,Nat.le_refl _,by omega,by omega,?_,?_,?_,Or.inl ⟨rfl,rfl⟩⟩
    · rw [caller,tailRun]
      rfl
    · rfl
    · exact built_fields post target plan bits keyPointer count _ _ rfl rfl rfl next

end InitECandidate.Solver.MutableTable.Layout32

#print axioms InitECandidate.Solver.MutableTable.Layout32.set_build
