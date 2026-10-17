import InitECandidate.Solver.WitnessRadix.AllocatedReadBounds
import InitECandidate.Solver.WitnessRadix.ReadFootprintStable

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- A later constructor's actual own-memory frame preserves the earlier radix
root, complete lookup representation and its read support. No equality with
the original program's private table contents is required. -/
theorem prior_radix_preserved (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (old : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready old) (table : Nat)
    (before : old.table+72+57*old.capacity+old.padding≤table)
    (stp pad out : BitVec 64)
    (stateArena : AllocatedBytes.Arena stp 200) (paddingArena : AllocatedBytes.Arena pad 136)
    (outputArena : AllocatedBytes.Arena out 32)
    (buffersBefore : stp.toNat+200≤old.records ∧ pad.toNat+136≤old.records ∧ out.toNat+32≤old.records)
    (domain : source.memaddrs=target.memaddrs) (endian : source.be=target.be)
    (root : BitVec 64) (tree : Graph.Tree)
    (rootMapped : source.memaddrs (BackingLayout.cell (AllocatedLayout.layout old) .header 24))
    (rootWord : source.memory (BackingLayout.cell (AllocatedLayout.layout old) .header 24)=.word root)
    (represented : QueryMemory.Represents source (AllocatedLayout.layout old).table (AllocatedLayout.layout old).keys
      (AllocatedLayout.layout old).vals root tree)
    (support : ∀ query,QueryMemory.reads source (AllocatedLayout.layout old).table (AllocatedLayout.layout old).keys
      (AllocatedLayout.layout old).vals root tree query → BackingLayout.Protected (AllocatedLayout.layout old) old.count query)
    (frame : ∀ query,query.toNat<table ∧ Keccak256.Protected stp pad out query → target.memory query=source.memory query) :
    target.memaddrs (BackingLayout.cell (AllocatedLayout.layout old) .header 24) ∧
      target.memory (BackingLayout.cell (AllocatedLayout.layout old) .header 24)=.word root ∧
      QueryMemory.Represents target (AllocatedLayout.layout old).table (AllocatedLayout.layout old).keys
        (AllocatedLayout.layout old).vals root tree ∧
      (∀ query,QueryMemory.reads target (AllocatedLayout.layout old).table (AllocatedLayout.layout old).keys
        (AllocatedLayout.layout old).vals root tree query → BackingLayout.Protected (AllocatedLayout.layout old) old.count query) := by
  have safe (query : BitVec 64) (saved : BackingLayout.Protected (AllocatedLayout.layout old) old.count query) :
      query.toNat<table ∧ Keccak256.Protected stp pad out query :=
    AllocatedLayout.protected_safe_for_later old ready old.count table (Nat.le_refl _) before stp pad out
      stateArena paddingArena outputArena buffersBefore query saved
  have agree : ∀ query,QueryMemory.reads source (AllocatedLayout.layout old).table (AllocatedLayout.layout old).keys
      (AllocatedLayout.layout old).vals root tree query → source.memory query=target.memory query := by
    intro query read
    exact (frame query (safe query (support query read))).symm
  refine ⟨by rw [←domain];exact rootMapped,?_,
    QueryMemory.represents_of_agreement source target domain endian _ _ _ root tree agree represented,?_⟩
  · exact (frame _ (safe _ (Or.inr (Or.inl rfl)))).trans rootWord
  · intro query read
    exact support query ((QueryMemory.reads_stable source target _ _ _ root tree agree query).mpr read)

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.prior_radix_preserved
