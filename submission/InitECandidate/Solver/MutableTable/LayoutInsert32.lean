import InitECandidate.Solver.MutableTable.LayoutTail32
import InitECandidate.Solver.MutableTable.ModelFrame32
import InitECandidate.Solver.MutableTable.InsertPreparedData
import InitECandidate.Solver.MutableTable.InsertLift32
import InitECandidate.Solver.MutableTable.InsertScanBound

namespace InitECandidate.Solver.MutableTable.Layout32
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Complete original raw insertion from represented bytes and constructor
layout. The real header/hash/scan/copy/stores/scopes are executed, reaching
an empty slot along an occupied path and paying at most order.length+3 clocks. -/
theorem insert_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (keyPointer : BitVec 64) (count : Nat) (countInside : count<plan.capacity) (value : BitVec 64)
    (header : Header source plan keyPointer count) (logical : Find.Model32 (BitVec 64))
    (model : Find.KeyModel32 source (parameters plan keyPointer) plan.capacity logical)
    (bits : Nat) (small : bits<64) (power : plan.capacity=2^bits)
    (order : List Nat) (room : order.length<plan.capacity) (covered : ∀ i<plan.capacity,logical i≠none→i∈order)
    (key : Find.Key32) (words : Fin 4→BitVec 64)
    (tLocal : source.locals.lookup (ofString "t")=some (.val (.word (BitVec.ofNat 64 plan.table))))
    (keyLocal : source.locals.lookup (ofString "key")=some (.val (.word keyPointer)))
    (valueLocal : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (aligned : keyPointer.toNat%8=0) (before : keyPointer.toNat+32≤plan.table) (little : source.be=false)
    (view : MemoryBytes.WordView source keyPointer words) (bytes : MemoryBytes.ByteView source keyPointer key)
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (copyCode : source.code.lookup (ofString "memcpy")=some (Copy32.formals,Copy32.body,.one))
    (enough : order.length+3≤source.clock) :
    ∃ stop target,stop≤order.length ∧
      evaluateHOLFiniteState source Insert.body=(some (.returned (.val (.word 0#64))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite
        {source with memory:=(resultMemory source.memory plan keyPointer
          (Probe.slot (2^bits) ((Hash.keyHash key).toNat%(2^bits)) stop) count value words),clock:=source.clock-(stop+3)} ∧
      logical (Probe.slot (2^bits) ((Hash.keyHash key).toNat%(2^bits)) stop)=none ∧
      ∀ step<Placement.distance (2^bits) ((Hash.keyHash key).toNat%(2^bits))
          (Probe.slot (2^bits) ((Hash.keyHash key).toNat%(2^bits)) stop),
        logical (Probe.slot (2^bits) ((Hash.keyHash key).toNat%(2^bits)) step)≠none := by
  let p:=parameters plan keyPointer
  let hash:=Hash.keyHash key
  let start:=hash.toNat%(2^bits)
  let orderPtr:=BitVec.ofNat 64 (base plan .order)
  let positionPtr:=BitVec.ofNat 64 (base plan .position)
  let entry:=Insert.prepared source p orderPtr positionPtr hash (hash &&& (p.capacity-1#64))
  have capacity : p.capacity=BitVec.ofNat 64 (2^bits):=by simp [p,parameters,TableEmpty.parameters,power]
  have entryModel : Find.KeyModel32 entry p (2^bits) logical := by
    rw [← power]
    exact key_model_fields source entry p plan.capacity logical rfl rfl rfl model
  have entryLocals : Find.Locals entry p (Find.pathIndex bits start 0) := by
    have indexEq : hash &&& (p.capacity-1#64)=Find.pathIndex bits start 0:=Find.masked_start p hash bits small capacity
    rw [← indexEq]
    exact Insert.prepared_locals source p orderPtr positionPtr hash _ keyLocal
  obtain ⟨stop,post,bound,scanRun,scanFrame,postLocals,empty,path,others⟩:=
    Insert.scan_model entry p bits start small (Nat.mod_lt _ (Nat.two_pow_pos bits)) capacity logical entryModel order
      (by simpa only [power] using room) (by simpa only [power] using covered) entryLocals
      (by change order.length≤source.clock-1;omega)
  let index:=Probe.slot (2^bits) start stop
  have indexInside : index<plan.capacity:=by rw [power];exact Nat.mod_lt _ (Nat.two_pow_pos bits)
  have memory : post.memory=source.memory:=congrArg (fun s=>s.memory) scanFrame
  have postDomain : post.memaddrs=source.memaddrs:=congrArg (fun s=>s.memaddrs) scanFrame
  have postEndian : post.be=source.be:=congrArg (fun s=>s.be) scanFrame
  have postCode : post.code=source.code:=congrArg (fun s=>s.code) scanFrame
  have postClock : post.clock=source.clock-1-stop:=congrArg (fun s=>s.clock) scanFrame
  have preparedData:=Insert.prepared_data source p (BitVec.ofNat 64 plan.table) orderPtr positionPtr hash (hash &&& (p.capacity-1#64)) value tLocal valueLocal
  have postT:= (others (ofString "t") (by decide)).trans preparedData.1
  have postValue:= (others (ofString "value") (by decide)).trans preparedData.2.1
  have postOrder:= (others (ofString "order") (by decide)).trans preparedData.2.2.1
  have postPosition:= (others (ofString "order_pos") (by decide)).trans preparedData.2.2.2
  obtain ⟨tailTarget,tailRun,tailFrame⟩:=tail_execute post plan ready (postDomain.trans domain) keyPointer index count indexInside countInside value words
    (header_fields source post plan keyPointer count memory.symm postDomain.symm header) postLocals postT postValue postOrder postPosition aligned before
    (postEndian.trans little) (word_view_fields source post keyPointer words memory.symm postDomain.symm view)
    (by rw [postCode];exact copyCode) (by omega)
  have suffixRun : evaluateHOLFiniteState entry Insert.afterIndex=(some (.returned (.val (.word 0#64))),tailTarget) := by
    rw [Insert.afterIndex,StateSteps.next_sequence entry post Insert.loop Insert.afterLoop scanRun (by change post.clock≤source.clock-1;omega)]
    exact tailRun
  let finalMemory:=resultMemory source.memory plan keyPointer index count value words
  have canonical : emptyLocalsHOLFinite {post with memory:=finalMemory,clock:=source.clock-1-stop-2}=
      emptyLocalsHOLFinite {source with memory:=finalMemory,clock:=source.clock-1-stop-2} := by
    have updated:=congrArg (fun s : PanSemStateFiniteExact 64 Guest.HostMemory=>
      emptyLocalsHOLFinite {s with memory:=finalMemory,clock:=source.clock-1-stop-2}) scanFrame
    exact updated
  have frame : emptyLocalsHOLFinite tailTarget=emptyLocalsHOLFinite
      {source with memory:=finalMemory,clock:=source.clock-1-(stop+2)} := by
    rw [memory,postClock] at tailFrame
    have arithmetic : source.clock-1-stop-2=source.clock-1-(stop+2):=by omega
    exact (tailFrame.trans canonical).trans (by rw [arithmetic])
  have cells:=Find.HeaderData.with_locals source source (BitVec.ofNat 64 plan.table) p header.find rfl rfl tLocal keyLocal
  have queryFits : keyPointer.toNat+32<2^64:=by have:=ready.fits;omega
  have mapped (offset : Nat) (inside : offset<72) (aligned : offset%8=0) :
      source.memaddrs (BitVec.ofNat 64 plan.table+BitVec.ofNat 64 offset) := by
    rw [header_cell plan offset]
    exact word_mapped source plan ready domain .header offset inside aligned
  obtain ⟨target,run,fullFrame⟩:=Insert.lift_tail32 source (BitVec.ofNat 64 plan.table) p orderPtr positionPtr cells rfl
    (mapped 56 (by decide) (by decide)) header.order (mapped 64 (by decide) (by decide)) header.position key bytes queryFits little hashCode
    (stop+2) finalMemory tailTarget suffixRun frame (by omega)
  refine ⟨stop,target,bound,run,?_,empty,path⟩
  have arithmetic : stop+2+1=stop+3:=by omega
  simpa only [arithmetic] using fullFrame

end InitECandidate.Solver.MutableTable.Layout32

#print axioms InitECandidate.Solver.MutableTable.Layout32.insert_execute
