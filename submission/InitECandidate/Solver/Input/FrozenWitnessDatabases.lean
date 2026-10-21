import InitECandidate.Solver.Input.MainRootBoundary
import InitECandidate.Solver.MutableTable.WitnessDatabaseBand

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open WitnessConstructors

/-- Immutable witness ownership below the heap frontier at materializer
entry. The current heap may advance, and already allocated MPT nodes above
this fixed frontier may be updated without touching either database. -/
def FrozenWitnessDatabases (input : Guest.InputBlob)
    (current : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier : Nat) : Prop :=
  ∃ codeArray nodeTable codeTable,
    MutableTable.WitnessBuild.Database current (VarList.decodedArray (DecoderCall.witnessArray input) (nodeBytes input)) nodeTable (nodeCount input) 1024 (nodeSlices input) 2713717584#64 ∧
    MutableTable.WitnessBuild.Database current (VarList.decodedArray codeArray (codeBytes input)) codeTable (codeCount input) 65536 (codeSlices input) 2713717584#64 ∧
    current.locals.lookup (ofString "db")=some (.val (.word nodeTable)) ∧
    MutableTable.WitnessBuild.BeforeHeap current nodeTable frontier ∧ MutableTable.WitnessBuild.BeforeHeap current codeTable frontier

theorem RootBoundary.freeze (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (boundary : RootBoundary input source) (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) :
    FrozenWitnessDatabases input source heap.toNat := by
  obtain ⟨codeArray,nodes,codes,actualHeap,nodeData,codeData,nodeCell,actualCell,arena,aligned,nodeBefore,codeBefore⟩:=boundary
  have heapEq : actualHeap=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
  subst actualHeap
  exact ⟨codeArray,nodes,codes,nodeData,codeData,nodeCell,nodeBefore,codeBefore⟩

/-- Rebuild the actual helper boundary at any genuine later aligned heap.
The immutable tables remain before their original frontier and hence before
the current heap; no old-node write is framed below the evolving heap. -/
theorem FrozenWitnessDatabases.boundary (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap : BitVec 64) (frozen : FrozenWitnessDatabases input current frontier)
    (heapCell : current.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (grows : frontier≤heap.toNat) : RootBoundary input current := by
  obtain ⟨codeArray,nodes,codes,nodeData,codeData,nodeCell,nodeBefore,codeBefore⟩:=frozen
  have advance (table : BitVec 64) (before : MutableTable.WitnessBuild.BeforeHeap current table frontier) :
      MutableTable.WitnessBuild.BeforeHeap current table heap.toNat:=by
    obtain ⟨capacity,cell,bound⟩:=before
    exact ⟨capacity,cell,bound.trans grows⟩
  exact ⟨codeArray,nodes,codes,heap,nodeData,codeData,nodeCell,heapCell,arena,aligned,advance nodes nodeBefore,advance codes codeBefore⟩

/-- Preserve both real databases by agreement only on their fixed physical
band. Scratch updates below it, allocations above its frontier and updates
to old MPT nodes above that frontier are all compatible with this frame. -/
theorem FrozenWitnessDatabases.frame (input : Guest.InputBlob)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier : Nat)
    (frozen : FrozenWitnessDatabases input source frontier)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (db : target.locals.lookup (ofString "db")=source.locals.lookup (ofString "db"))
    (memory : ∀ query : BitVec 64,2713717616≤query.toNat→query.toNat<frontier→target.memory query=source.memory query) :
    FrozenWitnessDatabases input target frontier := by
  obtain ⟨codeArray,nodes,codes,nodeData,codeData,nodeCell,nodeBefore,codeBefore⟩:=frozen
  have nodeKept:=nodeData.band_frame source target _ nodes _ _ _ 2713717584#64 frontier nodeBefore domain.symm endian.symm (by
    intro query lower upper
    change 2713717616≤query.toNat at lower
    exact memory query lower upper)
  have codeKept:=codeData.band_frame source target _ codes _ _ _ 2713717584#64 frontier codeBefore domain.symm endian.symm (by
    intro query lower upper
    change 2713717616≤query.toNat at lower
    exact memory query lower upper)
  exact ⟨codeArray,nodes,codes,nodeKept.1,codeKept.1,db.trans nodeCell,nodeKept.2,codeKept.2⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.RootBoundary.freeze
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.FrozenWitnessDatabases.boundary
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.FrozenWitnessDatabases.frame
