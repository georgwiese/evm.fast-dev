import InitECandidate.Solver.WitnessRadix.WordWrites
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack PanSemStateFiniteExact

inductive Field where
  | bytes (offset length : Nat)
  | scalar (offset : Nat)
  | wide (offset : Nat)
  | extra
  deriving DecidableEq

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

def FieldFacts (original : Memory) (header : BitVec 64) : Field→Prop
  | .bytes offset length=>offset≤240 ∧ offset%8=0 ∧ length≤256 ∧ WitnessRadix.AllocatedBytes.Arena (wordAt original (address header offset)) length
  | .scalar offset=>offset≤240 ∧ offset%8=0
  | .wide offset=>offset≤216 ∧ offset%8=0
  | .extra=>(wordAt original (address header 136)).toNat≤32 ∧
      WitnessRadix.AllocatedBytes.Arena (wordAt original (address header 128)) (wordAt original (address header 136)).toNat

def firstField : Field := .bytes 8 32
def baseRest : List Field := [
  .bytes 16 32,.bytes 24 20,.bytes 32 32,.bytes 40 32,.bytes 48 32,.bytes 56 256,
  .wide 64,.scalar 96,.scalar 104,.scalar 112,.scalar 120,.extra,.bytes 144 32,.bytes 152 8,
  .wide 160,.bytes 192 32,.scalar 200,.scalar 208,.bytes 216 32,.bytes 224 32]
def optionalFields : List Field := [.bytes 232 32,.scalar 240]

end InitECandidate.Solver.Input.HeaderEncoding
