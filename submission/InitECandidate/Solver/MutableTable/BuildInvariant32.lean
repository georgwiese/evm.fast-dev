import InitECandidate.Solver.MutableTable.LayoutInsert32
import InitECandidate.Solver.MutableTable.PlacementBuild
import InitECandidate.Solver.MutableTable.FindDictionary32

namespace InitECandidate.Solver.MutableTable.Layout32
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
attribute [local instance] Classical.propDecidable

/-- Physical original-table state and the logical insertion history agree.
The history, rather than the order array, supplies the probe covering list. -/
structure Built (bits : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (keyPointer : BitVec 64) (count : Nat) (input : List (Find.Key32×BitVec 64)) (logical : Find.Model32 (BitVec 64)) : Prop where
  header : Header source plan keyPointer count
  keys : Find.KeyModel32 source (parameters plan keyPointer) plan.capacity logical
  values : Find.ValueModel32 source (BitVec.ofNat 64 (base plan .values)) plan.capacity logical
  trace : Placement.Builds plan.capacity (Find.hashHome bits) input logical
  countBound : count≤input.length

/-- The actual completed table constructor starts the full physical and
logical build invariant at zero processed records. -/
theorem initial_built (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (shape : plan.capacity=4 ∨ plan.capacity%8=0) (little : source.be=false) (bits : Nat) (key : BitVec 64) :
    Built bits (TableNew.enteredState source plan) plan key 0 [] (fun _=>none) := by
  refine ⟨initial_header source plan ready domain key,TableEmpty.entered_model source plan ready shape domain little key,?_,.empty,by simp⟩
  intro i inside key value cell
  cases cell

/-- Complete original raw insertion extends the actual physical/logical
build invariant, with a bound from the number of processed records. -/
theorem insert_build (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (keyPointer : BitVec 64) (count : Nat) (input : List (Find.Key32×BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (bits : Nat) (small : bits<64) (power : plan.capacity=2^bits)
    (built : Built bits source plan keyPointer count input logical) (room : input.length<plan.capacity)
    (key : Find.Key32) (value : BitVec 64) (absent : lastValue key input=none) (words : Fin 4→BitVec 64)
    (tLocal : source.locals.lookup (ofString "t")=some (.val (.word (BitVec.ofNat 64 plan.table))))
    (keyLocal : source.locals.lookup (ofString "key")=some (.val (.word keyPointer)))
    (valueLocal : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (aligned : keyPointer.toNat%8=0) (before : keyPointer.toNat+32≤plan.table) (little : source.be=false)
    (view : MemoryBytes.WordView source keyPointer words) (bytes : MemoryBytes.ByteView source keyPointer key)
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (copyCode : source.code.lookup (ofString "memcpy")=some (Copy32.formals,Copy32.body,.one))
    (enough : input.length+3≤source.clock) :
    ∃ index paid target,index<plan.capacity ∧ paid≤input.length+3 ∧
      evaluateHOLFiniteState source Insert.body=(some (.returned (.val (.word 0#64))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite
        {source with memory:=resultMemory source.memory plan keyPointer index count value words,clock:=source.clock-paid} ∧
      Built bits target plan keyPointer (count+1) (input++[(key,value)]) (Placement.put logical index key value) := by
  classical
  obtain ⟨order,lengthBound,covered⟩:=Placement.build_cover plan.capacity (Find.hashHome bits) input logical built.trace
  have countInside : count<plan.capacity:=by have:=built.countBound;omega
  obtain ⟨stop,target,bound,run,frame,empty,path⟩:=insert_execute source plan ready domain keyPointer count countInside value built.header logical built.keys
    bits small power order (by omega) covered key words tLocal keyLocal valueLocal aligned before little view bytes hashCode copyCode (by omega)
  let index:=Probe.slot (2^bits) ((Hash.keyHash key).toNat%(2^bits)) stop
  have inside : index<plan.capacity:=by rw [power];exact Nat.mod_lt _ (Nat.two_pow_pos bits)
  have invariants:=Placement.build_invariants plan.capacity (Find.hashHome bits) input logical built.trace
  have only (query : Nat) (queryInside : query<plan.capacity) (old : BitVec 64) (stored : logical query=some (key,old)) : query=index := by
    have present:=invariants.2.1.1 query queryInside key old stored
    change lastValue key input=some old at present
    rw [absent] at present
    cases present
  have placedPath : ∀ step<Placement.distance plan.capacity (Find.hashHome bits key) index,
      logical (Probe.slot plan.capacity (Find.hashHome bits key) step)≠none := by
    simpa only [power,Find.hashHome] using path
  have trace : Placement.Builds plan.capacity (Find.hashHome bits) (input++[(key,value)]) (Placement.put logical index key value):=
    .snoc input logical built.trace index key value inside (Or.inl empty) only placedPath
  let changed:={source with memory:=resultMemory source.memory plan keyPointer index count value words}
  have memory : changed.memory=target.memory:=(congrArg (fun s=>s.memory) frame).symm
  have domainEq : changed.memaddrs=target.memaddrs:=(congrArg (fun s=>s.memaddrs) frame).symm
  have endian : changed.be=target.be:=(congrArg (fun s=>s.be) frame).symm
  have newHeader:=result_header source plan ready keyPointer index count inside countInside value words built.header
  have newKeys:=result_keys source plan ready domain keyPointer index count inside countInside logical key value words built.keys aligned
    (by have:=ready.fits;omega) little view bytes
  have newValues:=result_values source plan ready domain keyPointer index count inside countInside logical key value words built.values
  refine ⟨index,stop+3,target,inside,by omega,run,frame,?_,?_,?_,trace,?_⟩
  · exact header_fields changed target plan keyPointer (count+1) memory domainEq newHeader
  · exact key_model_fields changed target (parameters plan keyPointer) plan.capacity _ memory domainEq endian newKeys
  · exact value_model_fields changed target _ plan.capacity _ memory domainEq newValues
  · have:=built.countBound
    simp only [List.length_append,List.length_singleton]
    omega

end InitECandidate.Solver.MutableTable.Layout32

#print axioms InitECandidate.Solver.MutableTable.Layout32.insert_build
#print axioms InitECandidate.Solver.MutableTable.Layout32.initial_built
