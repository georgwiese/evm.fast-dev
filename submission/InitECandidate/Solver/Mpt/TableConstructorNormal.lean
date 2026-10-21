import InitECandidate.Solver.Mpt.NodeRegistryTableNew
import InitECandidate.Solver.MutableTable.TableRuntime.NormalRoom
import InitECandidate.Solver.MutableTable.WitnessBuildOriginalHelpers

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open MutableTable MutableTable.NaturalLayout WitnessCore

/-- The actual small original table-constructor scope derives all six
allocation reservations, its exact clock price and empty table model.
Every live trie node survives at the real continuation; room and future
callee success are never entry premises. -/
theorem table_call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (kind : KeyHash.Kind) (capacity : Nat) (positive : 0<capacity) (small : capacity≤256) (multiple : capacity%8=0)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (TableRuntime.values kind capacity))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_new") arguments continuation)=(some (.returned returned),post)) :
    let nextHeap:=BitVec.ofNat 64 (freshEnd kind heap.toNat capacity)
    let ready:=TableRuntime.callState source name kind heap.toNat capacity
    TableRuntime.price capacity+1≤source.clock ∧ Valid kind (fresh kind heap.toNat capacity) ∧
      AllocatedBytes.Arena nextHeap 0 ∧ nextHeap.toNat%8=0 ∧
      MemoryModel.Header ready.memory kind (fresh kind heap.toNat capacity) 0#64 ∧
      MemoryModel.Occupied ready kind (fresh kind heap.toNat capacity) [] ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → ready.memory query=source.memory query) ∧
      ∃ next : NodeRegistry ready frontier nextHeap db,next.graph.valid=registry.graph.valid ∧
        ∃ inner,evaluateHOLFiniteState ready continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  have helpers:=WitnessBuild.original_helpers source.code installed
  have allocation:=PersistentAlloc.original_code source.code installed
  have trap:=Input.Trap.original_code source.code installed
  have zero:=Zero.original_code source.code installed
  have keySmall : stride kind*capacity<2^64:=by
    have strideBound : stride kind≤64:=by cases kind <;> decide
    have product:=Nat.mul_le_mul strideBound small
    omega
  have wordSmall : 8*capacity<2^64:=by omega
  have capSmall : capacity+32<2^64:=by omega
  have actualHeap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 heap.toNat))):=by
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using heapCell
  have valid:=TableRuntime.normal_call_layout source post kind heap.toNat capacity name arguments continuation positive arena.lower (by have upper:=arena.upper; omega) aligned
    keySmall wordSmall capSmall multiple domain args helpers.tableCode actualHeap allocation trap zero returned normal
  obtain ⟨funded,inner,continued,endpoint⟩:=TableRuntime.call_normal source post kind heap.toNat capacity name arguments continuation valid domain (Or.inr multiple)
    args helpers.tableCode actualHeap allocation zero returned normal
  obtain ⟨next,same⟩:=registry.table_new source frontier heap db name kind heap.toNat capacity rfl valid
  have endBound : freshEnd kind heap.toNat capacity≤33806089496:=by
    have upper:=valid.upper .position
    simpa only [fresh,size,freshEnd] using upper
  have endNumber : (BitVec.ofNat 64 (freshEnd kind heap.toNat capacity)).toNat=freshEnd kind heap.toNat capacity:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have endArena : AllocatedBytes.Arena (BitVec.ofNat 64 (freshEnd kind heap.toNat capacity)) 0:=by
    constructor
    · rw [endNumber]
      have lower:=arena.lower
      dsimp only [freshEnd]; omega
    · rw [endNumber]; exact endBound
  have endAligned : (BitVec.ofNat 64 (freshEnd kind heap.toNat capacity)).toNat%8=0:=by
    rw [endNumber]
    have positionAligned:=valid.aligned .position
    change ((fresh kind heap.toNat capacity).base .position+8*capacity)%8=0
    simp [Nat.add_mod,Nat.mul_mod,positionAligned]
  exact ⟨funded,valid,endArena,endAligned,TableRuntime.caller_header source name kind heap.toNat capacity valid,
    TableRuntime.caller_model source name kind heap.toNat capacity valid (Or.inr multiple) domain little,
    fun query before=>TableRuntime.caller_memory_away source name kind heap.toNat capacity valid query (Or.inl before),next,same,inner,continued,endpoint⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.table_call_normal
