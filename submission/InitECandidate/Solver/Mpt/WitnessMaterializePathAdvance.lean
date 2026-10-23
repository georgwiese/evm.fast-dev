import InitECandidate.Solver.Mpt.WitnessMaterializePathOutput
import InitECandidate.Solver.Mpt.WitnessMaterializeOutputAdvance

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessCore WitnessCore.Stack Input.Main.RunAttemptConstructors

theorem PathOutput.advance_frame (input : Guest.InputBlob) (frontier : Nat) (db heap next root : BitVec 64)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : PathOutput input frontier db source returned) (returnedEq : returned=.val (.word root))
    (sourceHeap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (targetHeap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word next)))
    (arena : AllocatedBytes.Arena next 0) (aligned : next.toNat%8=0) (grows : heap.toNat≤next.toNat)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (scratch : ∃ cursor,target.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)))
    (memory : ∀ query : BitVec 64,2713717616≤query.toNat → query.toNat<frontier → target.memory query=source.memory query)
    (kind : root≠0#64 → target.memory root=source.memory root)
    (registry : NodeRegistry target frontier next db) (paths : registry.PathModel) (member : registry.graph.valid root) : PathOutput input frontier db target returned :=
  ⟨output.1.advance_frame input frontier db heap next root source target returned returnedEq sourceHeap targetHeap arena aligned grows domain endian scratch memory kind,
    next,root,returnedEq,targetHeap,registry,paths,member⟩

end InitECandidate.Solver.Mpt.WitnessMaterialize

#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.PathOutput.advance_frame
