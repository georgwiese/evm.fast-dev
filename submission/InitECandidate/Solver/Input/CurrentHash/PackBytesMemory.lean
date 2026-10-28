import InitECandidate.Solver.Input.CurrentHash.PackBytesReturn
import InitECandidate.Solver.Input.CurrentHash.MemoryGlobals
import InitECandidate.Solver.Input.PackBytesEnvironment
import InitECandidate.Solver.Input.ZeroShortMemory
import InitECandidate.Solver.Input.CopyAwaySubrange
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal

namespace InitECandidate.Solver.Input.CurrentHash.PackBytesMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open PackBytes

theorem buffer_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor query : BitVec 64) (n : Nat)
    (small : n+64<2^64) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (data : PackBytesCost.Locals source p cursor n)
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (padded n)) (aligned : cursor.toNat%8=0)
    (away : CopyGeneral.Away cursor query (padded n))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterBuffer=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe : LocalPrefix (ofString "buf") (.call (some (none,none)) (ofString "memcpy") copyArguments) := .call none _ _ (by intro name impossible; cases impossible)
  rw [body_shape.2.2.1] at actual
  obtain ⟨middle,copyRun,remaining⟩ := Input.sequence_returned source post _ afterCopy value (safe.summary_full source).2.1 actual
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) copyArguments=some (CopyGeneral.values cursor p n) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,copyArguments,localVar,data.pointer,data.buf,data.length,CopyGeneral.values]
  have bounds := padding_bounds n
  have copied := MemoryAt.copy_normal source middle copyArguments p cursor query n args installed domain inputArena
    (AllocatedBytes.Arena.weaken cursor (padded n) n arena bounds.1) (by intro offset inside; exact away offset (by omega)) copyRun
  have next := data.after_call _ _ copyRun
  have fields := evaluation_fields source middle _ none copyRun
  have zeroArgs := PackBytesArguments.zero_arguments middle cursor n small next.buf next.length next.count
  have geometry := padding_geometry cursor n arena aligned
  rw [body_shape.2.2.2] at remaining
  have zeroSafe : LocalPrefix (ofString "buf") (.call (some (none,none)) (ofString "memzero") zeroArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨final,zeroRun,returned⟩ := Input.sequence_returned middle post _ _ value (zeroSafe.summary_full middle).2.1 remaining
  have cleared := ZeroShort.call_memory middle final zeroArguments (cursor+BitVec.ofNat 64 n) query (padded n-n) (by omega) zeroArgs
    (fields.2.2.2.symm ▸ installed) (fields.1.trans domain) geometry.1 geometry.2.2
    (CopyGeneral.Away.subrange cursor query (padded n) n (padded n-n) away (by omega)) zeroRun
  have tail := MemoryAt.return_current final (.rstruct [localVar "buf",localVar "count"]) query
  rw [returned] at tail
  exact tail.trans (cleared.trans copied)

theorem buffer_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code afterBuffer := by
  rw [body_shape.2.2.1,body_shape.2.2.2]
  exact GlobalEffects.sequence key code _ _ (MemoryGlobals.call .copy key code installed (some none) _)
    (GlobalEffects.sequence key code _ _ (MemoryGlobals.call .zero key code installed (some none) _) (GlobalEffects.returned key code _))

structure Returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor query : BitVec 64) (n : Nat) (value : ValueHOL 64) : Prop where
  tuple : value = PackBytesReturn.tuple cursor n
  room : cursor.toNat+padded n ≤ 2952790016
  heap : post.globals.lookup (ofString "heap_ptr") = some (.val (.word (PersistentAlloc.rounded cursor (BitVec.ofNat 64 (padded n)))))
  grows : cursor.toNat+padded n ≤ (PersistentAlloc.rounded cursor (BitVec.ofNat 64 (padded n))).toNat
  nextBound : (PersistentAlloc.rounded cursor (BitVec.ofNat 64 (padded n))).toNat ≤ 2952790016
  nextAligned : (PersistentAlloc.rounded cursor (BitVec.ofNat 64 (padded n))).toNat%8 = 0
  protectedWord : post.memory query = source.memory query

/-- A genuine current pack return derives its persistent allocation room,
actual tuple and next aligned heap, while preserving earlier metadata words. -/
theorem body_image (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor query : BitVec 64) (n : Nat)
    (small : n+64<2^64) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (length : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (heapLower : 2701131776≤cursor.toNat) (heapBound : cursor.toNat≤2952790016) (aligned : cursor.toNat%8=0)
    (inputArena : AllocatedBytes.Arena p n) (below : query.toNat<cursor.toNat)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source body=(some (.returned value),post)) : Returned source post cursor query n value := by
  rw [body_shape.1] at actual
  obtain ⟨declaredPost,declarationRun,declarationEndpoint⟩ := declaration_return_word source post "count" countExpression
    (BitVec.ofNat 64 (chunks n)) afterCount value (count_read_bounded source n (by omega) length) actual
  let declared := bind source "count" (BitVec.ofNat 64 (chunks n))
  change evaluateHOLFiniteState declared afterCount = (some (.returned value),declaredPost) at declarationRun
  have countLocal : declared.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 (chunks n)))) := bind_lookup_same _ _ _
  have args : evalListHOLFinite declared (h:=fun address=>Classical.propDecidable (declared.memaddrs address)) [amountExpression] =
      some (PersistentAlloc.values (BitVec.ofNat 64 (padded n))) := by
    have read := PackBytesArguments.amount_read declared n countLocal
    simp only [eval] at read
    simp only [evalListHOLFinite,evalListHOLExact,PersistentAlloc.values,read]
  rw [body_shape.2.1] at declarationRun
  obtain ⟨room,positive,inner,remaining,allocationEndpoint⟩ := PersistentAlloc.call_normal declared declaredPost "buf" [amountExpression] afterBuffer cursor
    (BitVec.ofNat 64 (padded n)) args (PersistentAlloc.original_code declared.code installed) (Trap.original_code declared.code installed)
    heap heapBound value declarationRun
  have bounds := padding_bounds n
  have paddedNumber : (BitVec.ofNat 64 (padded n)).toNat = padded n := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [paddedNumber] at room
  have arena : AllocatedBytes.Arena cursor (padded n) := ⟨heapLower,by omega⟩
  let allocated := PersistentAlloc.post {declared with clock:=declared.clock-1} cursor (BitVec.ofNat 64 (padded n))
  let entry := bind allocated "buf" cursor
  have kept (name : String) (notBuf : ofString "buf"≠ofString name) (notCount : ofString "count"≠ofString name) :
      entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
    (bind_lookup_other allocated "buf" name cursor notBuf).trans (bind_lookup_other source "count" name _ notCount)
  have data : PackBytesCost.Locals entry p cursor n := ⟨(kept "p" (by decide) (by decide)).trans pointer,bind_lookup_same _ _ _,
    (kept "n" (by decide) (by decide)).trans length,(bind_lookup_other allocated "buf" "count" cursor (by decide)).trans countLocal⟩
  have preserved := buffer_memory entry inner p cursor query n small installed domain data inputArena arena aligned
    (CopyGeneral.Away.after cursor query (padded n) aligned (by omega) below) value remaining
  have tuple := PackBytesReturn.buffer_return entry inner p cursor n data value remaining
  have same := buffer_globals (ofString "heap_ptr") entry.code installed entry rfl
  rw [remaining] at same
  have heapPost : inner.globals.lookup (ofString "heap_ptr") = some (.val (.word (PersistentAlloc.rounded cursor (BitVec.ofNat 64 (padded n))))) :=
    (congrArg Prod.snd same).trans (by
      change (declared.globals.update (ofString "heap_ptr", .val (.word (PersistentAlloc.rounded cursor (BitVec.ofNat 64 (padded n)))))).lookup (ofString "heap_ptr") = _
      simp [HolFiniteMapExact.lookup_update,FUPDATE])
  have guards := PersistentAlloc.guards cursor (BitVec.ofNat 64 (padded n)) (by rw [paddedNumber]; exact room)
  refine ⟨tuple,room,?_,?_,guards.2.2.2.1,guards.2.2.2.2,?_⟩
  · rw [declarationEndpoint,allocationEndpoint]
    exact heapPost
  · simpa only [paddedNumber] using guards.2.2.1
  · rw [declarationEndpoint,allocationEndpoint]
    exact preserved

theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor query : BitVec 64) (n : Nat)
    (small : n+64<2^64) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (length : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (heapLower : 2701131776≤cursor.toNat) (heapBound : cursor.toNat≤2952790016) (aligned : cursor.toNat%8=0)
    (inputArena : AllocatedBytes.Arena p n) (below : query.toNat<cursor.toNat)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source body=(some (.returned value),post)) : post.memory query=source.memory query :=
  (body_image source post p cursor query n small installed domain pointer length heap heapLower heapBound aligned inputArena below value actual).protectedWord

theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor query : BitVec 64) (n : Nat)
    (small : n+64<2^64) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (heapLower : 2701131776≤cursor.toNat) (heapBound : cursor.toNat≤2952790016) (aligned : cursor.toNat%8=0)
    (inputArena : AllocatedBytes.Arena p n) (below : query.toNat<cursor.toNat) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p n))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "pack_bytes") arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,pLocal,nLocal⟩ := environment source.code.lookup p n (original_code source.code installed)
  exact MemoryAt.call_normal source post (ofString "pack_bytes") arguments (values p n) body callee returnShape query args called
    (fun target value evaluated => body_memory (callEntryStateHOLFinite source callee) target p cursor query n small installed domain pLocal nLocal heap
      heapLower heapBound aligned inputArena below value evaluated) actual

end InitECandidate.Solver.Input.CurrentHash.PackBytesMemory

#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesMemory.buffer_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesMemory.body_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesMemory.call_memory

#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesMemory.buffer_globals
#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesMemory.body_image
