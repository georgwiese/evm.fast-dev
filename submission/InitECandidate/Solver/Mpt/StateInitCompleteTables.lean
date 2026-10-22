import InitECandidate.Solver.Mpt.StateInitNormal
import InitECandidate.Solver.Mpt.StateInitTableFamily

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable MutableTable.NaturalLayout
open Flapjack.Basis.Pure.MlString GasBudget.Journal

def storageObject (storage : BitVec 64) : TableFamily.Object:=⟨.word,fresh .word storage.toNat 64,[],storage.toNat⟩
def blockPointer (storage : BitVec 64) : BitVec 64:=BitVec.ofNat 64 (freshEnd .word storage.toNat 64)
def initializedObjects (storage : BitVec 64):=Block.allObjects (blockPointer storage) (storageObject storage)
def journalBase (storage : BitVec 64) : Nat:=(PersistentAlloc.rounded (blockPointer storage) 80#64).toNat+70840+64

/-- All eight actual initialized tables, including the earlier workspace
storage cache, share the genuine final heap and are disjoint from the
entire reserved journal. This is derived from the whole normal initializer. -/
theorem Output.table_family (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (workspace nodes rootHash codes : BitVec 64) (output : Output input source post workspace nodes rootHash codes) :
    ∃ heap storage,post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      TableFamily.Model post heap.toNat (initializedObjects storage) ∧
      Zone (initializedObjects storage) (journalBase storage) Initialization.capacity heap.toNat:=by
  obtain ⟨installed,scalars,scratch,globals,code,domain,endian,oracle,heap,root,storage,heapCell,arena,aligned,view,frozen,table,bs,
    registry,member,regions,block,older,workspaceBefore⟩:=output
  have bounded : freshEnd .word storage.toNat 64≤33806089496:=table.valid.upper .position
  have blockNumber : (blockPointer storage).toNat=freshEnd .word storage.toNat 64:=by
    rw [blockPointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have family:=block.add_older_table post (blockPointer storage) workspace (storageObject storage) heap.toNat table (by
    intro pool
    rewrite [blockNumber]
    exact (fresh_bounds .word storage.toNat 64 pool).2)
  exact ⟨heap,storage,heapCell,family⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.Output.table_family
