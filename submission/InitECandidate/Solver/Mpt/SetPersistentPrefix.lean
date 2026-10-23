import InitECandidate.Solver.Mpt.SetHeader
import InitECandidate.Solver.Mpt.TrieProtectedBelow
import InitECandidate.Solver.Input.FrozenWitnessDatabases

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix
open WitnessRadix.QueryBranch Input.Main.RunAttemptConstructors

/-- The actual setter retains every word in the older persistent band,
including caller tables and witness databases. The low scratch pool and
the map's deliberately updated root are outside this band. -/
theorem Output.persistent_prefix (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (value : ValueHOL 64) (m incoming length : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower cutoff : Nat)
    (property : BitVec 64→BitVec 64→Prop) (allowance : Nat)
    (output : Output source target value m graph incoming incoming length limit nodeLower pathLower property allowance)
    (frontier : AllocatedBytes.Arena incoming 0) (aligned : incoming.toNat%8=0) (small : length.toNat≤64)
    (regions : graph.Regions nodeLower incoming.toNat) (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower incoming.toNat)
    (cutoffAligned : cutoff%8=0) (nodesAbove : cutoff≤nodeLower) (pathsAbove : cutoff≤pathLower)
    (cutoffBefore : cutoff≤incoming.toNat) (headerAbove : cutoff≤m.toNat) :
    ∀ address : BitVec 64,DeleteFrame.ceiling≤address.toNat→address.toNat<cutoff→target.memory address=source.memory address := by
  intro address above before
  have safe:=TrieWalk.Graph.ProtectedWord.below_regions graph source.be nodeLower pathLower incoming.toNat cutoff address
    regions paths pathRegions cutoffAligned nodesAbove pathsAbove before
  have framed:=output.older_word source target value m incoming length graph limit nodeLower pathLower property allowance frontier aligned small address safe above (before.trans_le cutoffBefore)
  exact framed.1 (by intro same; have numbers:=congrArg BitVec.toNat same; omega)

/-- Whole original updates preserve the actual immutable witness
databases for the next root decode at the same fixed frontier. -/
theorem Output.frozen_databases (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (value : ValueHOL 64) (m incoming length db : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower cutoff : Nat)
    (property : BitVec 64→BitVec 64→Prop) (allowance : Nat)
    (output : Output source target value m graph incoming incoming length limit nodeLower pathLower property allowance)
    (frontier : AllocatedBytes.Arena incoming 0) (aligned : incoming.toNat%8=0) (small : length.toNat≤64)
    (regions : graph.Regions nodeLower incoming.toNat) (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower incoming.toNat)
    (cutoffAligned : cutoff%8=0) (nodesAbove : cutoff≤nodeLower) (pathsAbove : cutoff≤pathLower)
    (cutoffBefore : cutoff≤incoming.toNat) (headerAbove : cutoff≤m.toNat)
    (frozen : FrozenWitnessDatabases input (bind source "db" db) cutoff) :
    FrozenWitnessDatabases input (bind target "db" db) cutoff := by
  apply frozen.frame input (bind source "db" db) (bind target "db" db) cutoff output.domain output.endian
    ((bind_lookup_same target "db" db).trans (bind_lookup_same source "db" db).symm)
  exact output.persistent_prefix source target value m incoming length graph limit nodeLower pathLower cutoff property allowance
    frontier aligned small regions paths pathRegions cutoffAligned nodesAbove pathsAbove cutoffBefore headerAbove

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.Output.persistent_prefix
#print axioms InitECandidate.Solver.Mpt.SetTrie.Output.frozen_databases
