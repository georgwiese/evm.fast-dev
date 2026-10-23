import InitECandidate.Solver.Mpt.TriePathBytesSeparation
import InitECandidate.Solver.Mpt.TrieGraphPathBytes

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- A current path buffer may be borrowed by a new leaf or extension.
Its bytes and backing words are protected from every live mutable node. -/
structure Graph.PathBuffer {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (be : Bool) (lower upper : Nat) (pointer : BitVec 64) (length : Nat) : Prop where
  span : NibbleSpan memory domain be pointer length
  bounds : lower≤pointer.toNat ∧ pointer.toNat+length≤upper
  apart : ∀ index<length,∀ owner,graph.valid owner → owner≠0#64 → ∀ offset<nodeBytes (wordAt memory owner),
    panByteAlignHOL (width:=64) (byteAddress pointer index)≠byteAddress owner offset

theorem Graph.PathBuffer.stored {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (be : Bool) (lower upper : Nat)
    (paths : graph.PathBytes be) (regions : graph.PathRegions lower upper) (separated : graph.PathSeparated)
    (node : BitVec 64) (member : graph.valid node) (active : node≠0#64)
    (tag : wordAt memory node=1#64 ∨ wordAt memory node=2#64) :
    graph.PathBuffer be lower upper (wordAt memory (node+32#64)) (wordAt memory (node+40#64)).toNat :=
  ⟨paths.span node member active tag,regions node member active tag,separated node member active tag⟩

/-- A split borrows an actual window, including unaligned suffixes. -/
theorem Graph.PathBuffer.window {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (be : Bool) (lower upper : Nat) (pointer position : BitVec 64) (length count : Nat)
    (buffer : graph.PathBuffer be lower upper pointer length) (bounded : position.toNat≤length) (within : count≤length-position.toNat) :
    graph.PathBuffer be lower upper (pointer+position) count := by
  have addition : (pointer+position).toNat=pointer.toNat+position.toNat:=
    BitVec.toNat_add_of_lt (by have fits:=buffer.span.fits; omega)
  refine ⟨buffer.span.window memory domain be pointer position length count bounded within,?_,?_⟩
  · rw [addition]
    have bounds:=buffer.bounds
    omega
  · intro index inside owner member active offset offsetInside
    have shifted : byteAddress (pointer+position) index=byteAddress pointer (position.toNat+index):=by
      simp [byteAddress,BitVec.ofNat_add,BitVec.add_assoc]
    rw [shifted]
    exact buffer.apart _ (by omega) owner member active offset offsetInside

/-- A freshly allocated query buffer follows every old node. Its own
pointer may already have been shifted; only the heap frontier is aligned. -/
theorem Graph.PathBuffer.fresh {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (be : Bool) (nodeLower lower upper : Nat) (pointer : BitVec 64) (length : Nat)
    (regions : graph.Regions nodeLower lower) (aligned : lower%8=0)
    (span : NibbleSpan memory domain be pointer length) (above : lower≤pointer.toNat) (before : pointer.toNat+length≤upper) :
    graph.PathBuffer be lower upper pointer length := by
  refine ⟨span,⟨above,before⟩,?_⟩
  intro index inside owner member active offset offsetInside same
  obtain ⟨floor,arena,ownerAligned,endBefore⟩:=regions owner member active
  have number:=byteAddress_toNat pointer index (by have fits:=span.fits; omega)
  have ownerNumber:=byteAddress_toNat owner offset (by have fits:=arena.upper; omega)
  have equal:=congrArg BitVec.toNat same
  rw [AllocatedBytes.aligned_number,number,ownerNumber] at equal
  omega

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBuffer.stored
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBuffer.window
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBuffer.fresh
