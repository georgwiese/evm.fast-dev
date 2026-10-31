import InitECandidate.Solver.Input.MemoryMetadata
import InitECandidate.Solver.Input.CurrentStartup.ArenaState
import InitECandidate.Solver.Arenas.ScopedNone
import InitECandidate.Solver.WitnessRadix.AllocationDomain

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Ordinary words above the incoming scratch cursor are untouched. -/
def Above (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff : Nat) : Prop :=
  ∀ query,cutoff≤query.toNat → target.memory query=source.memory query

theorem Above.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff : Nat) : Above source source cutoff := fun _ _=>rfl
theorem Above.trans (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff : Nat)
    (first : Above source middle cutoff) (second : Above middle target cutoff) : Above source target cutoff :=
  fun query upper=>(second query upper).trans (first query upper)


/-- Runtime fields retained by scratch work, apart from its temporary
cursor globals, memory contents, locals and clock. -/
def scratchMetadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  Input.MemoryMetadata.erase {source with globals := HolFiniteMapExact.empty}

/-- Actual scratch work retains the runtime and protects both sides of the
interval between the frame cursor and entering scratch cursor. -/
structure Outside (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat) : Prop where
  runtime : scratchMetadata target = scratchMetadata source
  memory : ∀ query, query.toNat < lower ∨ upper ≤ query.toNat → target.memory query = source.memory query

instance {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {lower upper : Nat} :
    CoeFun (Outside source target lower upper)
      (fun _ => ∀ query : BitVec 64, query.toNat < lower ∨ upper ≤ query.toNat → target.memory query = source.memory query) where
  coe frame := frame.memory

theorem Outside.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat) :
    Outside source source lower upper := ⟨rfl, fun _ _ => rfl⟩

theorem Outside.of_readonly {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (lower upper : Nat)
    (frame : Input.LocalEffects.erase target = Input.LocalEffects.erase source) : Outside source target lower upper := by
  have runtime := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    {state with globals := HolFiniteMapExact.empty}) (Input.MemoryMetadata.of_frame frame)
  exact ⟨runtime, fun query _ => congrFun (Input.LocalEffects.memory_of_erase source target frame) query⟩

/-- Current original scratch/frame cursors and fixed ordinary domain.
These entry facts do not assert room for a future record allocation. -/
structure Arena (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64) : Prop where
  domain : source.memaddrs=InitE.ordinaryDomain
  cursorGlobal : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor))
  limitGlobal : source.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word limit))
  ordered : limit.toNat≤cursor.toNat
  aligned : limit.toNat%8=0
  lower : 2701131776≤limit.toNat
  upper : cursor.toNat≤33806089496

theorem Arena.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Arena source cursor limit) (domain : target.memaddrs=source.memaddrs) (globals : target.globals=source.globals) : Arena target cursor limit :=
  ⟨domain.trans arena.domain,by rw [globals]; exact arena.cursorGlobal,by rw [globals]; exact arena.limitGlobal,
    arena.ordered,arena.aligned,arena.lower,arena.upper⟩

theorem Arena.record_bounds (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Arena source cursor limit) (room : Arenas.Room .down cursor limit 24#64) :
    let pointer := Arenas.rounded .down cursor 24#64
    pointer≠0#64 ∧ pointer.toNat+24<2^64 ∧ pointer.toNat+24≤cursor.toNat ∧
      limit.toNat≤pointer.toNat ∧ pointer.toNat%8=0 := by
  obtain ⟨first,second,lower,upper,padding,aligned⟩ := Arenas.downward_guards cursor limit 24#64 arena.aligned room
  change (Arenas.rounded .down cursor 24#64).toNat+24≤cursor.toNat at upper
  refine ⟨?_,by have := arena.upper; omega,upper,lower,aligned⟩
  intro zero
  rw [zero] at lower
  have := arena.lower
  change _≤0 at lower
  omega

theorem Arena.record_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Arena source cursor limit) (room : Arenas.Room .down cursor limit 24#64) (offset : Nat)
    (inside : offset+8≤24) (aligned : offset%8=0) :
    source.memaddrs (Arenas.rounded .down cursor 24#64+BitVec.ofNat 64 offset) := by
  obtain ⟨active,fits,below,lower,pointerAligned⟩ := Arena.record_bounds source cursor limit arena room
  let pointer := Arenas.rounded .down cursor 24#64
  change pointer.toNat+24<2^64 at fits
  change pointer.toNat+24≤cursor.toNat at below
  change limit.toNat≤pointer.toNat at lower
  change pointer.toNat%8=0 at pointerAligned
  have offsetSmall : offset<2^64 := by omega
  have number : (pointer+BitVec.ofNat 64 offset).toNat=pointer.toNat+offset := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt offsetSmall]; change pointer.toNat+offset<2^64; omega),
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt offsetSmall]
  rw [arena.domain]
  apply WitnessRadix.BackingLayout.ordinary_mapped
  · rw [number]; have := arena.lower; change limit.toNat≤pointer.toNat at lower; omega
  · rw [number]; have := arena.upper; change pointer.toNat+24≤cursor.toNat at below; omega
  · rw [number,Nat.add_mod,pointerAligned,aligned]

theorem Arena.after_allocation (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Arena source cursor limit) (room : Arenas.Room .down cursor limit 24#64) :
    Arena (Arenas.post source .down cursor 24#64) (Arenas.rounded .down cursor 24#64) limit := by
  obtain ⟨active,fits,below,lower,aligned⟩ := Arena.record_bounds source cursor limit arena room
  refine ⟨arena.domain,?_,?_,lower,arena.aligned,arena.lower,?_⟩
  · simp [Arenas.post,Arenas.pointerName,HolFiniteMapExact.update,FUPDATE]
  · simpa [Arenas.post,Arenas.pointerName,HolFiniteMapExact.update,FUPDATE,
      show ofString "scratch_ptr"≠ofString "frame_mem_ptr" from by decide] using arena.limitGlobal
  · have := arena.upper
    omega

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.Arena.of_fields
#print axioms InitECandidate.Solver.Rlp.Validation.Arena.record_bounds
#print axioms InitECandidate.Solver.Rlp.Validation.Arena.record_mapped
#print axioms InitECandidate.Solver.Rlp.Validation.Arena.after_allocation

#print axioms InitECandidate.Solver.Rlp.Validation.Outside.refl

#print axioms InitECandidate.Solver.Rlp.Validation.Outside.of_readonly

namespace InitECandidate.Solver.Rlp
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Live scratch cursors stay within the current main scratch region. No
room for a future allocation, original cursor value or empty stack is assumed. -/
structure LiveArena (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  domain : source.memaddrs=InitE.ordinaryDomain
  code : Input.OriginalCode.Installed source.code
  cursors : ∃ cursor limit,Validation.Arena source cursor limit ∧
    2952790016≤limit.toNat ∧ cursor.toNat≤2965299200

namespace LiveArena

theorem of_validation {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor limit : BitVec 64}
    (arena : Validation.Arena source cursor limit) (lower : 2952790016≤limit.toNat)
    (upper : cursor.toNat≤2965299200) (installed : Input.OriginalCode.Installed source.code) : LiveArena source :=
  ⟨arena.domain,installed,cursor,limit,arena,lower,upper⟩

theorem of_startup {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    (arena : Input.CurrentStartup.ArenaState source) : LiveArena source :=
  ⟨arena.domain,arena.code,2965299200#64,2952790016#64,
    ⟨arena.domain,arena.scratch,arena.frame,by decide,by decide,by decide,by decide⟩,by decide,by decide⟩

instance {source : PanSemStateFiniteExact 64 Guest.HostMemory} :
    Coe (Input.CurrentStartup.ArenaState source) (LiveArena source) := ⟨of_startup⟩

theorem of_metadata {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (arena : LiveArena source) (metadata : Input.MemoryMetadata.erase target=Input.MemoryMetadata.erase source) : LiveArena target := by
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change target.globals=source.globals at globals
  obtain ⟨cursor,limit,physical,lower,upper⟩:=arena.cursors
  exact of_validation (physical.of_fields source target cursor limit (Input.MemoryMetadata.domain metadata) globals)
    lower upper (by rw [Input.MemoryMetadata.code metadata]; exact arena.code)

theorem of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (arena : LiveArena source) (frame : Input.LocalEffects.erase target=Input.LocalEffects.erase source) : LiveArena target :=
  arena.of_metadata (Input.MemoryMetadata.of_frame frame)

/-- The actual cursor globals select the region bounds supplied by the
live arena, even when the caller names those cursors separately. -/
theorem bounds {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor limit : BitVec 64}
    (live : LiveArena source) (arena : Validation.Arena source cursor limit) :
    2952790016≤limit.toNat ∧ cursor.toNat≤2965299200 := by
  obtain ⟨actualCursor,actualLimit,actual,lower,upper⟩:=live.cursors
  have cursorEq : actualCursor=cursor := by
    simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using Option.some.inj (actual.cursorGlobal.symm.trans arena.cursorGlobal)
  have limitEq : actualLimit=limit := by
    simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using Option.some.inj (actual.limitGlobal.symm.trans arena.limitGlobal)
  subst actualCursor actualLimit
  exact ⟨lower,upper⟩

/-- Allocating persistent heap may change its own global while retaining
the real live scratch/frame globals, runtime domain and installed code. -/
theorem of_cursors {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (live : LiveArena source) (domain : target.memaddrs=source.memaddrs) (code : target.code=source.code)
    (scratch : target.globals.lookup (ofString "scratch_ptr")=source.globals.lookup (ofString "scratch_ptr"))
    (frame : target.globals.lookup (ofString "frame_mem_ptr")=source.globals.lookup (ofString "frame_mem_ptr")) : LiveArena target := by
  obtain ⟨cursor,limit,physical,lower,upper⟩:=live.cursors
  have next : Validation.Arena target cursor limit:=
    ⟨domain.trans physical.domain,scratch.trans physical.cursorGlobal,frame.trans physical.limitGlobal,
      physical.ordered,physical.aligned,physical.lower,physical.upper⟩
  exact of_validation next lower upper (by rw [code]; exact live.code)

end LiveArena

/-- Enlarging the protected scratch interval retains its runtime frame and
protects both the earlier persistent heap and any live records above it. -/
theorem Validation.Outside.widen {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {lower upper wideLower wideUpper : Nat} (outside : Validation.Outside source target lower upper)
    (below : wideLower≤lower) (above : upper≤wideUpper) : Validation.Outside source target wideLower wideUpper :=
  ⟨outside.runtime,fun query location=>outside query (location.elim
    (fun before=>Or.inl (Nat.lt_of_lt_of_le before below))
    (fun after=>Or.inr (Nat.le_trans above after)))⟩

end InitECandidate.Solver.Rlp

#print axioms InitECandidate.Solver.Rlp.LiveArena.of_validation
#print axioms InitECandidate.Solver.Rlp.LiveArena.of_startup
#print axioms InitECandidate.Solver.Rlp.LiveArena.of_metadata
#print axioms InitECandidate.Solver.Rlp.LiveArena.of_frame
#print axioms InitECandidate.Solver.Rlp.Validation.Outside.widen

#print axioms InitECandidate.Solver.Rlp.LiveArena.bounds
#print axioms InitECandidate.Solver.Rlp.LiveArena.of_cursors
