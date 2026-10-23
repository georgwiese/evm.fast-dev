import InitECandidate.Solver.Mpt.DeleteFrameEntry
import InitECandidate.Solver.Mpt.TrieGraphPathBand

namespace InitECandidate.Solver.Mpt.DeleteFrame
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget

/-- The actual allocated record preserves the entire persistent graph
and its complete stored paths. Only actual room, derived by push_entry
from a continuing call, is needed to locate the scratch writes. -/
theorem stored_paths (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor frame : BitVec 64) (words : String→BitVec 64)
    (arena : Rlp.Validation.Arena source cursor frame) (before : cursor.toNat≤ceiling)
    (room : Arenas.Room .down cursor frame 40#64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower upper : Nat)
    (property : BitVec 64→BitVec 64→Prop) (values : TrieWalk.Values graph limit property)
    (regions : graph.Regions nodeLower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower upper) (separated : graph.PathSeparated)
    (nodesAbove : ceiling≤nodeLower) (pathsAbove : ceiling≤pathLower) :
    ∃ next : TrieWalk.Graph (stored kind source cursor words).memory (stored kind source cursor words).memaddrs,
      next.valid=graph.valid ∧ next.Regions nodeLower upper ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
        next.PathBytes (stored kind source cursor words).be ∧ next.PathRegions pathLower upper ∧ next.PathSeparated := by
  apply graph.after_path_band source (stored kind source cursor words) limit nodeLower pathLower upper ceiling property
    values regions disjoint paths pathRegions separated (by decide) nodesAbove pathsAbove rfl rfl
  intro query lower _upper
  exact allocated_writes_above kind source.memory cursor frame words arena.lower before arena.aligned room query (before.trans lower)

/-- A fresh scratch record also retains an arbitrary unaligned query
buffer in the persistent band, including its separation from node fields. -/
theorem stored_buffer (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor frame : BitVec 64) (words : String→BitVec 64)
    (arena : Rlp.Validation.Arena source cursor frame) (before : cursor.toNat≤ceiling)
    (room : Arenas.Room .down cursor frame 40#64)
    (graph : TrieWalk.Graph source.memory source.memaddrs)
    (next : TrieWalk.Graph (stored kind source cursor words).memory (stored kind source cursor words).memaddrs)
    (nodeLower lower upper : Nat) (pointer : BitVec 64) (length : Nat)
    (regions : graph.Regions nodeLower upper) (nodesAbove : ceiling≤nodeLower)
    (buffer : graph.PathBuffer source.be lower upper pointer length) (pathsAbove : ceiling≤lower)
    (same : next.valid=graph.valid) : next.PathBuffer (stored kind source cursor words).be lower upper pointer length := by
  have memory (query : BitVec 64) (above : ceiling≤query.toNat) :
      (stored kind source cursor words).memory query=source.memory query:=
    allocated_writes_above kind source.memory cursor frame words arena.lower before arena.aligned room query (before.trans above)
  apply buffer.of_aligned_band source (stored kind source cursor words) graph next lower upper ceiling pointer length same
    (by intro node member active; unfold wordAt; rw [memory node (nodesAbove.trans (regions node member active).1)])
    (by decide) pathsAbove rfl rfl
  intro query above _upper
  exact memory query above

/-- Actual downward allocation and writes extend the same physical PREV
chain. This connects the semantic push memory to the finite stack model. -/
theorem stored_stack (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor frame : BitVec 64) (words : String→BitVec 64)
    (arena : Rlp.Validation.Arena source cursor frame) (before : cursor.toNat≤ceiling)
    (room : Arenas.Room .down cursor frame 40#64) (frames : List Saved)
    (stack : Stack source cursor.toNat (words "top") frames) :
    let record:=Arenas.resultWord .down cursor 40#64
    Stack (stored kind source cursor words) record.toNat record (⟨record,kind,words⟩::frames) := by
  obtain ⟨recordArena,recordAligned,_,recordBefore,_,_⟩:=allocated_bounds cursor frame arena.lower before arena.aligned room
  have view : Saved.View (stored kind source cursor words) ⟨Arenas.resultWord .down cursor 40#64,kind,words⟩:=
    Saved.View.of_written (allocated kind source cursor) ⟨Arenas.resultWord .down cursor 40#64,kind,words⟩ recordArena recordAligned (recordBefore.trans before)
  exact stack.push source (stored kind source cursor words) cursor.toNat (words "top") frames _ view rfl recordBefore
    (by intro query above _upper; exact allocated_writes_above kind source.memory cursor frame words arena.lower before arena.aligned room query above)

end InitECandidate.Solver.Mpt.DeleteFrame

#print axioms InitECandidate.Solver.Mpt.DeleteFrame.stored_paths
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.stored_buffer
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.stored_stack
