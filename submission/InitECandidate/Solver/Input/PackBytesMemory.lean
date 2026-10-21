import InitECandidate.Solver.Input.ZeroShortMemory
import InitECandidate.Solver.Input.PackBytesCallCost
import InitECandidate.Solver.Input.CopyAwaySubrange
import InitECandidate.Solver.Input.IgnoredCallLookup

namespace InitECandidate.Solver.Input.PackBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Original copy, possibly unaligned short padding and tuple return all
preserve a word outside the actual allocated packed buffer. -/
theorem buffer_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor query : BitVec 64) (n : Nat)
    (small : n≤134217728) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (chunksLocal : source.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 (chunks n)))))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (padded n)) (aligned : cursor.toNat%8=0)
    (away : CopyGeneral.Away cursor query (padded n))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterBuffer=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe : LocalPrefix (ofString "buf") (.call (some (none,none)) (ofString "memcpy") copyArguments) := .call none _ _ (by intro name impossible; cases impossible)
  rw [body_shape.2.2.1] at run
  obtain ⟨middle,copyRun,remaining⟩ := Input.sequence_returned source post _ afterCopy value (safe.summary_full source).2.1 run
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) copyArguments=some (CopyGeneral.values cursor p n) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,copyArguments,localVar,pointer,buffer,count,CopyGeneral.values]
  have bounds := padding_bounds n
  have copied := MemoryAt.copy_normal source middle copyArguments p cursor query n args installed domain inputArena
    (AllocatedBytes.Arena.weaken cursor (padded n) n arena bounds.1)
    (by intro offset inside; exact away offset (by omega)) copyRun
  have other (name : String) : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    CallNormal.ignored_lookup source middle (ofString name) (ofString "memcpy") copyArguments copyRun
  have fields := evaluation_fields source middle _ none copyRun
  have zeroArgs := zero_arguments middle cursor n small ((other "buf").trans buffer) ((other "n").trans count) ((other "count").trans chunksLocal)
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

/-- Whole unchanged pack_bytes body preserves every protected input or
decoded word below its actual allocation cursor, on a genuine normal return. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor query : BitVec 64) (n : Nat)
    (small : n≤134217728) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (padded n)) (aligned : cursor.toNat%8=0)
    (below : query.toNat<cursor.toNat)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) : post.memory query=source.memory query := by
  obtain ⟨paid,final,remaining,endpoint⟩ := allocation_prefix source post cursor n small count installed heap arena (some (.returned value)) run (by simp)
  let entry := buffered source cursor n
  have cells := buffered_fields source cursor n
  have current := buffer_memory entry final p cursor query n small installed domain
    ((buffered_other source cursor n "p" (by decide) (by decide)).trans pointer) cells.1
    ((buffered_other source cursor n "n" (by decide) (by decide)).trans count) cells.2.1 inputArena arena aligned
    (CopyGeneral.Away.after cursor query (padded n) aligned (by have h:=arena.upper; omega) below) value remaining
  rw [endpoint]
  exact current

/-- Actual normal original pack caller inherits the allocated-buffer frame. -/
theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor query : BitVec 64) (n : Nat)
    (small : n≤134217728) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (padded n)) (aligned : cursor.toNat%8=0)
    (below : query.toNat<cursor.toNat) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p n))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "pack_bytes") arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,pLocal,nLocal⟩ := environment source.code.lookup p n (original_code source.code installed)
  exact MemoryAt.call_normal source post (ofString "pack_bytes") arguments (values p n) body callee returnShape query args called
    (fun target value evaluated=>body_memory (callEntryStateHOLFinite source callee) target p cursor query n small installed domain pLocal nLocal heap inputArena arena aligned below value evaluated) run

end InitECandidate.Solver.Input.PackBytes

#print axioms InitECandidate.Solver.Input.PackBytes.buffer_memory
#print axioms InitECandidate.Solver.Input.PackBytes.body_memory
#print axioms InitECandidate.Solver.Input.PackBytes.call_memory
