import InitECandidate.Solver.Input.HeaderEncoding.Program

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

abbrev Memory := WitnessRadix.WordWrites.Memory
def wordAt (memory : Memory) (address : BitVec 64) : BitVec 64 := WitnessRadix.MemoryBytes.wordBits (memory address)
def address (header : BitVec 64) (offset : Nat) : BitVec 64 := header+BitVec.ofNat 64 offset
def cursor (buffer : BitVec 64) : BitVec 64 := buffer+1024#64

structure Geometry (header buffer : BitVec 64) : Prop where
  headerLower : 2701131776≤header.toNat
  headerAligned : header.toNat%8=0
  headerBefore : header.toNat+248≤buffer.toNat
  bufferAligned : buffer.toNat%8=0
  room : buffer.toNat+1056≤33806089496

def OldMemory (current original : Memory) (buffer : BitVec 64) : Prop :=
  ∀ query,query.toNat<buffer.toNat→current query=original query

structure Context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64) : Prop where
  geometry : Geometry header buffer
  domain : source.memaddrs=InitE.ordinaryDomain
  oldMemory : OldMemory source.memory original buffer
  headerLocal : source.locals.lookup (ofString "h")=some (.val (.word header))
  heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor buffer)))

def FieldFacts (original : Memory) (header : BitVec 64) : Field→Prop
  | .bytes offset length=>offset≤240 ∧ offset%8=0 ∧ length≤256 ∧ WitnessRadix.AllocatedBytes.Arena (wordAt original (address header offset)) length
  | .scalar offset=>offset≤240 ∧ offset%8=0
  | .wide offset=>offset≤216 ∧ offset%8=0
  | .extra=>(wordAt original (address header 136)).toNat≤32 ∧
      WitnessRadix.AllocatedBytes.Arena (wordAt original (address header 128)) (wordAt original (address header 136)).toNat

theorem Geometry.buffer_arena (header buffer : BitVec 64) (geometry : Geometry header buffer) : WitnessRadix.AllocatedBytes.Arena buffer 1056 :=
  ⟨by have h:=geometry.headerLower; have b:=geometry.headerBefore; omega,geometry.room⟩

theorem Geometry.header_address (header buffer : BitVec 64) (geometry : Geometry header buffer) (offset : Nat) (inside : offset≤240) :
    (address header offset).toNat=header.toNat+offset :=
  WitnessRadix.byteAddress_toNat header offset (by have b:=geometry.headerBefore; have r:=geometry.room; omega)

theorem Context.cell (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64)
    (context : Context source original header buffer) (offset : Nat) (inside : offset≤240) (aligned : offset%8=0) :
    source.memaddrs (address header offset) ∧ source.memory (address header offset)=.word (wordAt original (address header offset)) := by
  have number:=context.geometry.header_address header buffer offset inside
  have lower:=context.geometry.headerLower
  have before:=context.geometry.headerBefore
  have room:=context.geometry.room
  constructor
  · rw [context.domain]
    apply WitnessRadix.BackingLayout.ordinary_mapped
    · rw [number]; omega
    · rw [number]; omega
    · rw [number,Nat.add_mod,context.geometry.headerAligned,aligned]
  · rw [context.oldMemory _ (by rw [number]; omega)]
    cases stored : original (address header offset) with
    | word value=>simp [wordAt,stored,WitnessRadix.MemoryBytes.wordBits]

/-- Any aligned word before the fresh buffer is outside all actual byte/word
writes in a later ordinary-memory range. Boundary alignment is explicit. -/
theorem before_away (dst query : BitVec 64) (length boundary : Nat) (arena : WitnessRadix.AllocatedBytes.Arena dst length)
    (after : boundary≤dst.toNat) (aligned : boundary%8=0) (before : query.toNat<boundary) :
    RlpWrite.BytesWrite.Away dst query length := by
  intro offset inside
  have number:=WitnessRadix.byteAddress_toNat dst offset (by have h:=arena.upper; omega)
  have alignedNumber:=WitnessRadix.AllocatedBytes.aligned_number (dst+BitVec.ofNat 64 offset)
  change (dst+BitVec.ofNat 64 offset).toNat=dst.toNat+offset at number
  have qdiv:=Nat.mod_add_div boundary 8
  have adiv:=Nat.mod_add_div (dst.toNat+offset) 8
  have amod:=Nat.mod_lt (dst.toNat+offset) (by decide : 0<8)
  constructor
  · intro equal
    have native:=congrArg BitVec.toNat equal
    rw [number] at native
    omega
  · intro equal
    have native:=congrArg BitVec.toNat equal
    rw [alignedNumber,number] at native
    omega

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.Geometry.buffer_arena
#print axioms InitECandidate.Solver.Input.HeaderEncoding.Geometry.header_address
#print axioms InitECandidate.Solver.Input.HeaderEncoding.Context.cell
#print axioms InitECandidate.Solver.Input.HeaderEncoding.before_away
