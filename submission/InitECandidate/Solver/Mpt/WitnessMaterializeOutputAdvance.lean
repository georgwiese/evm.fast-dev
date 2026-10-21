import InitECandidate.Solver.Mpt.WitnessMaterializeRichOutput

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessCore WitnessCore.Stack Input.Main.RunAttemptConstructors

/-- Actual later allocation may advance heap while a root cache changes.
Only the frozen database prefix and nonnull result tag must agree; the
real new heap/scratch fields and node geometry are checked explicitly. -/
theorem Output.advance_frame (input : Guest.InputBlob) (frontier : Nat) (db heap next root : BitVec 64)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : Output input frontier db source returned) (returnedEq : returned=.val (.word root))
    (sourceHeap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (targetHeap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word next)))
    (arena : AllocatedBytes.Arena next 0) (aligned : next.toNat%8=0) (grows : heap.toNat≤next.toNat)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (scratch : ∃ cursor,target.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)))
    (memory : ∀ query : BitVec 64,2713717616≤query.toNat → query.toNat<frontier → target.memory query=source.memory query)
    (kind : root≠0#64 → target.memory root=source.memory root) : Output input frontier db target returned := by
  obtain ⟨actualHeap,child,valueEq,heapCell,oldArena,oldAligned,frontierBefore,oldScratch,frozen,owned⟩:=output
  have sameHeap : actualHeap=heap := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (heapCell.symm.trans sourceHeap)))
  subst actualHeap
  have sameChild : child=root := HolWordLab.word.inj (ValueHOL.val.inj (valueEq.symm.trans returnedEq))
  subst child
  have frozenTarget:=frozen.frame input (QueryBranch.bind source "db" db) (QueryBranch.bind target "db" db) frontier domain endian
    ((bind_lookup_same target "db" db).trans (bind_lookup_same source "db" db).symm) memory
  have nextOwned : ResultOwned target frontier next.toNat root := by
    rcases owned with zero|allocated
    · exact Or.inl zero
    · obtain ⟨tag,stored,bounded⟩:=allocated.kind
      by_cases zero : root=0#64
      · exact Or.inl zero
      · exact Or.inr ⟨allocated.arena,allocated.aligned,allocated.fresh,allocated.before.trans grows,tag,(kind zero).trans stored,bounded⟩
  exact ⟨next,root,returnedEq,targetHeap,arena,aligned,frontierBefore.trans grows,scratch,frozenTarget,nextOwned⟩

theorem RichOutput.advance_frame (input : Guest.InputBlob) (frontier : Nat) (db heap next root : BitVec 64)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : RichOutput input frontier db source returned) (returnedEq : returned=.val (.word root))
    (sourceHeap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (targetHeap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word next)))
    (arena : AllocatedBytes.Arena next 0) (aligned : next.toNat%8=0) (grows : heap.toNat≤next.toNat)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (scratch : ∃ cursor,target.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)))
    (memory : ∀ query : BitVec 64,2713717616≤query.toNat → query.toNat<frontier → target.memory query=source.memory query)
    (kind : root≠0#64 → target.memory root=source.memory root)
    (registry : NodeRegistry target frontier next db) (member : registry.graph.valid root) : RichOutput input frontier db target returned :=
  ⟨output.1.advance_frame input frontier db heap next root source target returned returnedEq sourceHeap targetHeap arena aligned grows domain endian scratch memory kind,
    next,root,returnedEq,targetHeap,registry,member⟩

end InitECandidate.Solver.Mpt.WitnessMaterialize

#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.Output.advance_frame
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.RichOutput.advance_frame
