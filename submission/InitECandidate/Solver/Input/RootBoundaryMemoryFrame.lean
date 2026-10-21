import InitECandidate.Solver.Input.MainRootBoundary
import InitECandidate.Solver.MutableTable.WitnessDatabaseBand

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Freeze the existing database band while scratch storage below it and
fresh persistent storage above it change. The new real heap word/geometry
and its monotone advance supply the caller's updated frontier. -/
theorem RootBoundary.memory_frame (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier next : BitVec 64) (actual : RootBoundary input source)
    (sourceHeap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word frontier)))
    (targetHeap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word next)))
    (arena : AllocatedBytes.Arena next 0) (aligned : next.toNat%8=0) (grows : frontier.toNat≤next.toNat)
    (domain : source.memaddrs=target.memaddrs) (endian : source.be=target.be)
    (db : target.locals.lookup (ofString "db")=source.locals.lookup (ofString "db"))
    (memory : ∀ query : BitVec 64,2713717616≤query.toNat→query.toNat<frontier.toNat→target.memory query=source.memory query) :
    RootBoundary input target := by
  obtain ⟨codeArray,nodes,codes,heap,nodeDatabase,codeDatabase,nodeCell,heapCell,heapArena,heapAligned,nodeBefore,codeBefore⟩ := actual
  have valueEq:=Option.some.inj (heapCell.symm.trans sourceHeap)
  have heapEq : heap=frontier := HolWordLab.word.inj (ValueHOL.val.inj valueEq)
  subst heap
  have nodeData:=nodeDatabase.band_frame source target _ nodes _ _ _ 2713717584#64 frontier.toNat nodeBefore domain endian (by
    intro query lower upper
    change 2713717616≤query.toNat at lower
    exact memory query lower upper)
  have codeData:=codeDatabase.band_frame source target _ codes _ _ _ 2713717584#64 frontier.toNat codeBefore domain endian (by
    intro query lower upper
    change 2713717616≤query.toNat at lower
    exact memory query lower upper)
  have advance (table : BitVec 64) (before : MutableTable.WitnessBuild.BeforeHeap target table frontier.toNat) :
      MutableTable.WitnessBuild.BeforeHeap target table next.toNat := by
    obtain ⟨capacity,cell,bound⟩ := before
    exact ⟨capacity,cell,bound.trans grows⟩
  exact ⟨codeArray,nodes,codes,next,nodeData.1,codeData.1,db.trans nodeCell,targetHeap,arena,aligned,advance nodes nodeData.2,advance codes codeData.2⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.RootBoundary.memory_frame
