import InitECandidate.Solver.Mpt.WsAccountLeafData
import InitECandidate.Solver.Mpt.WsAccountLeafAllocCost
import InitECandidate.Solver.Mpt.TrieLookupMemory
import InitECandidate.Solver.Input.HeapScopeMemory
import InitECandidate.Solver.Input.TrapCost
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal

namespace InitECandidate.Solver.Mpt.WsAccountLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Ordinary memory outside the real hash buffers/output and nibble buffer. -/
def MemoryFrame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad h nibs : BitVec 64) : Prop :=
  ∀ query,Keccak256.Protected stp pad h query →
    (∀ offset<64,query≠panByteAlignHOL (width:=64) (byteAddress nibs offset)) → post.memory query=source.memory query

theorem finish_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source finish=(some (.returned returned),post)) : post.memory=source.memory := by
  have safe : Input.LocalPrefix (ofString "r") (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) :=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,released,tailRun,locals⟩ := safe.normal_continue source post (.return (localVar "r")) returned normal
  have memory := Input.HeapScope.ignored_release_memory source middle [localVar "mark"] installed released
  rw [(Input.return_normal middle post (localVar "r") returned tailRun).2]
  exact memory

/-- Normal lookup and its real release/return continuation preserve every
ordinary word outside the nibble conversion's backing words. -/
theorem lookup_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root h nibs : BitVec 64)
    (data : Data source ws root h nibs)
    (outputCell : source.locals.lookup (ofString "h")=some (.val (.word h)))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source lookup=(some (.returned returned),post)) :
    ∀ query,(∀ offset<64,query≠panByteAlignHOL (width:=64) (byteAddress nibs offset)) → post.memory query=source.memory query := by
  have args := lookup_arguments source ws root h data.worldState data.rootMapped data.rootStored outputCell
  obtain ⟨target,answer,inner,frame,finishRun,restored⟩ := TrieLookup.scoped_memory source post root h nibs data.scratch data.little data.fits
    data.inputMapped data.outputMapped data.separate "r" lookupArguments finish args installed returned normal
  let ready := Input.CallNormal.continuationEntry source target "r" answer
  have codeEq := congrArg PanSemStateFiniteExact.code frame.fields
  change target.code=source.code at codeEq
  have readyInstalled : Input.OriginalCode.Installed ready.code := by change Input.OriginalCode.Installed target.code; rw [codeEq]; exact installed
  have memory := finish_memory ready inner readyInstalled returned finishRun
  intro query outside
  rw [restored]
  change inner.memory query=source.memory query
  rw [memory]
  exact frame.memory query outside

/-- Actual address hashing, nibble conversion, read-only trie traversal and
heap release compose to the complete suffix memory frame. -/
theorem after_alloc_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr h nibs stp pad : BitVec 64)
    (data : Data source ws root h nibs) (hashData : Keccak256.EntryData source stp addr pad h 20)
    (graphProtection : ∀ query,data.graph.Footprint query → Keccak256.Protected stp pad h query)
    (rootProtection : Keccak256.Protected stp pad h (ws+24#64))
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word addr)))
    (outputCell : source.locals.lookup (ofString "h")=some (.val (.word h)))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterAlloc=(some (.returned returned),post)) : MemoryFrame source post stp pad h nibs := by
  have safe : Input.LocalPrefix (ofString "h") hash := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨reached,hashRun,lookupRun,localEq⟩ := safe.normal_continue source post lookup returned normal
  have args := hash_arguments source addr h addressCell outputCell
  obtain ⟨locals,upper,lower,control,memory⟩ := Keccak256.call_normal source reached hashArguments stp addr pad h 20 args
    (hash_original_code source.code installed) hashData (by decide) hashRun
  obtain ⟨nextData⟩ := Data.after_hash source reached ws root h nibs stp pad data graphProtection rootProtection control memory
  have currentH : reached.locals.lookup (ofString "h")=some (.val (.word h)) := by rw [locals]; exact outputCell
  have codeEq := congrArg PanSemStateFiniteExact.code control
  change reached.code=source.code at codeEq
  have currentInstalled : Input.OriginalCode.Installed reached.code := by rw [codeEq]; exact installed
  have lookupFrame := lookup_memory reached post ws root h nibs nextData currentH currentInstalled returned lookupRun
  intro query guarded outside
  exact (lookupFrame query outside).trans (memory query guarded)

set_option maxRecDepth 100000 in
/-- The actual allocator exposes the real hash/lookup continuation and
retains its complete ordinary-memory frame through lexical restoration. -/
theorem after_mark_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr h nibs stp pad : BitVec 64)
    (data : Data source ws root h nibs)
    (hashData : Keccak256.EntryData source stp addr pad h 20)
    (graphProtection : ∀ query,data.graph.Footprint query → Keccak256.Protected stp pad h query)
    (rootProtection : Keccak256.Protected stp pad h (ws+24#64))
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word addr)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word h)))
    (heapBound : h.toNat≤33806089496)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterMark=(some (.returned returned),post)) :
    MemoryFrame source post stp pad h nibs := by
  classical
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [.const 32#64]=some (PersistentAlloc.values 32#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  obtain ⟨room,positive,inner,tailRun,restored⟩ := PersistentAlloc.call_normal source post "h" [.const 32#64] afterAlloc h 32#64 args
    (alloc_original_code source.code installed) (Input.Trap.original_code source.code installed) heap heapBound returned normal
  change h.toNat+32≤33806089496 at room
  let ready := bind (PersistentAlloc.post {source with clock := source.clock-1} h 32#64) "h" h
  have otherGlobal (name : String) (different : ofString "heap_ptr"≠ofString name) :
      ready.globals.lookup (ofString name)=source.globals.lookup (ofString name) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded h 32#64)))).lookup (ofString name)=_
    simp [HolFiniteMapExact.update,FUPDATE,different]
  let readyData := Data.of_fields source ready ws root h nibs data rfl rfl rfl (otherGlobal "ws" (by decide)) (otherGlobal "mpt_nib_scratch" (by decide))
  have readyHashData := Keccak256.EntryData.of_fields source ready stp addr pad h 20 rfl rfl rfl
    (otherGlobal "keccak_st" (by decide)) (otherGlobal "keccak_pad" (by decide)) hashData
  have readyGraphProtection : ∀ query,readyData.graph.Footprint query → Keccak256.Protected stp pad h query := graphProtection
  have readyAddress : ready.locals.lookup (ofString "addr")=some (.val (.word addr)) :=
    (bind_lookup_other _ "h" "addr" h (by decide)).trans addressCell
  have readyOutput : ready.locals.lookup (ofString "h")=some (.val (.word h)) := bind_lookup_same _ _ _
  have answer := after_alloc_memory ready inner ws root addr h nibs stp pad readyData readyHashData
    readyGraphProtection rootProtection readyAddress readyOutput installed returned tailRun
  rw [restored]
  exact answer

set_option maxRecDepth 100000 in
/-- Complete original account-leaf lookup preserves all words outside its
actual hash and nibble buffers, including after the saved mark is released. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr h nibs stp pad : BitVec 64)
    (data : Data source ws root h nibs)
    (hashData : Keccak256.EntryData source stp addr pad h 20)
    (graphProtection : ∀ query,data.graph.Footprint query → Keccak256.Protected stp pad h query)
    (rootProtection : Keccak256.Protected stp pad h (ws+24#64))
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word addr)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word h)))
    (heapBound : h.toNat≤33806089496)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    MemoryFrame source post stp pad h nibs := by
  rw [body_shape] at normal
  have positive := Input.CallNormal.normal_clock source post (ofString "mark") .one (ofString "heap_mark") [] afterMark returned normal
  let ready := bind {source with clock := source.clock-1} "mark" h
  let inner := (evaluateHOLFiniteState ready afterMark).2
  have actual := Input.HeapScope.mark_call_execute source h "mark" afterMark heap (Input.HeapScope.mark_original_code source.code installed) positive
  have joined := actual.symm.trans normal
  have resultEq := congrArg Prod.fst joined
  change (evaluateHOLFiniteState ready afterMark).1=some (.returned returned) at resultEq
  have innerRun : evaluateHOLFiniteState ready afterMark=(some (.returned returned),inner) := Prod.ext resultEq rfl
  have postEq := (congrArg Prod.snd joined).symm
  change post=restore source "mark" inner at postEq
  let readyData := Data.of_fields source ready ws root h nibs data rfl rfl rfl rfl rfl
  have readyHashData := Keccak256.EntryData.of_fields source ready stp addr pad h 20 rfl rfl rfl rfl rfl hashData
  have readyGraphProtection : ∀ query,readyData.graph.Footprint query → Keccak256.Protected stp pad h query := graphProtection
  have readyAddress : ready.locals.lookup (ofString "addr")=some (.val (.word addr)) :=
    (bind_lookup_other _ "mark" "addr" h (by decide)).trans addressCell
  have answer := after_mark_memory ready inner ws root addr h nibs stp pad readyData readyHashData
    readyGraphProtection rootProtection readyAddress heap heapBound installed returned innerRun
  rw [postEq]
  exact answer

end InitECandidate.Solver.Mpt.WsAccountLeaf

#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.finish_memory
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.lookup_memory
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.after_alloc_memory

#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.after_mark_memory
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.body_memory
