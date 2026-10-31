import InitECandidate.Solver.Mpt.WitnessMaterializeOutput

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessCore WitnessCore.Stack Input.Main.RunAttemptConstructors

/-- Actual later allocation may advance heap while a root cache changes.
Only the frozen database prefix and nonnull result tag must agree; the
real new heap/scratch fields and node geometry are checked explicitly. -/
theorem Output.advance_frame (data : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db heap next root : BitVec 64)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : Output data frontier db source returned) (returnedEq : returned=.val (.word root))
    (sourceHeap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (targetHeap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word next)))
    (arena : AllocatedBytes.Arena next 0) (bounded : next.toNat≤2952790016) (aligned : next.toNat%8=0) (grows : heap.toNat≤next.toNat)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (scratch : ∃ cursor,target.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)))
    (memory : ∀ query : BitVec 64,query.toNat<frontier → target.memory query=source.memory query)
    (kind : root≠0#64 → target.memory root=source.memory root) : Output data frontier db target returned := by
  obtain ⟨actualHeap,child,valueEq,heapCell,oldArena,oldBound,oldAligned,frontierBefore,oldScratch,tableBefore,database,owned⟩:=output
  have sameHeap : actualHeap=heap := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (heapCell.symm.trans sourceHeap)))
  subst actualHeap
  have sameChild : child=root := HolWordLab.word.inj (ValueHOL.val.inj (valueEq.symm.trans returnedEq))
  subst child
  have databaseTarget:=database.of_before frontier tableBefore domain endian memory
  have nextOwned : ResultOwned target frontier next.toNat root := by
    rcases owned with zero|allocated
    · exact Or.inl zero
    · obtain ⟨tag,stored,bounded⟩:=allocated.kind
      by_cases zero : root=0#64
      · exact Or.inl zero
      · exact Or.inr ⟨allocated.arena,allocated.aligned,allocated.fresh,allocated.before.trans grows,tag,(kind zero).trans stored,bounded⟩
  exact ⟨next,root,returnedEq,targetHeap,arena,bounded,aligned,frontierBefore.trans grows,scratch,tableBefore,databaseTarget,nextOwned⟩

end InitECandidate.Solver.Mpt.WitnessMaterialize

#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.Output.advance_frame
