import InitECandidate.Solver.Mpt.WitnessCoreRegistryBranchFinish

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Separation from every actual cell of a bounded node excludes the
entire numeric interval, including unaligned path backing words. -/
theorem outside_node_of_away (query node : BitVec 64) (size : Nat) (arena : AllocatedBytes.Arena node size)
    (away : ∀ offset<size,query≠byteAddress node offset) :
    query.toNat<node.toNat ∨ node.toNat+size≤query.toNat := by
  by_contra outside
  have lower : node.toNat≤query.toNat:=by omega
  have upper : query.toNat<node.toNat+size:=by omega
  let offset:=query.toNat-node.toNat
  have inside : offset<size:=by omega
  have number:=byteAddress_toNat node offset (by have bound:=arena.upper; omega)
  have same : byteAddress node offset=query:=by
    apply BitVec.eq_of_toNat_eq
    rw [number]
    omega
  exact away offset inside same.symm

/-- A full path's backing word can begin seven bytes before its byte
pointer. That still lies strictly above the real scratch OCC write. -/
theorem branch_counter_path_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record node child : BitVec 64) (index : Fin 16) (occupied : Fin 17)
    (arena : AllocatedBytes.Arena node 176) (ceiling : record.toNat+88≤2713717616)
    (query : BitVec 64) (floor : 2713731425≤query.toNat) (outside : query.toNat<node.toNat ∨ node.toNat+176≤query.toNat) :
    (branchCounterEntry source record node child index occupied).memory query=source.memory query := by
  have childNumber : (WitnessRecord.childAddress node index).toNat=node.toNat+(32+8*index.val):=
    byteAddress_toNat node _ (by have upper:=arena.upper; have bound:=index.isLt; omega)
  have recordNumber : (record+40#64).toNat=record.toNat+40:=byteAddress_toNat record 40 (by omega)
  apply branch_counter_entry_memory source record node child index occupied query
  · intro equal
    have numeric:=congrArg BitVec.toNat equal
    rw [childNumber] at numeric
    have bound:=index.isLt
    omega
  · intro equal
    have numeric:=congrArg BitVec.toNat equal
    rw [recordNumber] at numeric
    omega

/-- The actual parser and final branch fields preserve those same full
backing words outside the pending node; no stronger pointer alignment is
assumed merely to reuse a narrower old-memory frame. -/
theorem branch_finished_path_memory (source built : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node previous cursor header bytes flag : BitVec 64) (data : WitnessRecord.Description) (occupied : Fin 17)
    (arena : AllocatedBytes.Arena node 176) (below : cursor.toNat≤2713717616)
    (above : Rlp.Validation.Above source built cursor.toNat) (query : BitVec 64) (floor : 2713731425≤query.toNat)
    (outside : query.toNat<node.toNat ∨ node.toNat+176≤query.toNat) :
    (branchFinishedState source built node previous data header bytes flag occupied).memory query=source.memory query := by
  have away (offset : Nat) (inside : offset<176) : query≠node+BitVec.ofNat 64 offset:=by
    have number : (node+BitVec.ofNat 64 offset).toNat=node.toNat+offset:=byteAddress_toNat node offset (by have upper:=arena.upper; omega)
    intro equal
    have numeric:=congrArg BitVec.toNat equal
    rw [number] at numeric
    omega
  exact (branch_finished_field_memory source built node previous data header bytes flag occupied query
    (away 8 (by decide)) (away 16 (by decide)) (away 160 (by decide)) (away 168 (by decide))).trans (above query (by omega))

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.outside_node_of_away
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_counter_path_memory
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_finished_path_memory
