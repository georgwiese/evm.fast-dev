import InitECandidate.Solver.Mpt.StateInitProgram
import InitECandidate.Solver.WitnessRadix.AllocationGlobalExecution
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.WitnessRadix.AllocatedBytes
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) :=
  Input.putGlobal (PersistentAlloc.post {source with clock:=source.clock-1} heap 40#64) "ws" heap
def written (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (offset : Nat) (word : BitVec 64) :=
  {source with memory:=StoreWord.put source.memory (heap+BitVec.ofNat 64 offset) word}
def ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nodes root codes : BitVec 64) :=
  written (written (written (allocated source heap) heap 0 nodes) heap 8 root) heap 16 codes

theorem store_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (offset : Nat) (name : String) (word : BitVec 64)
    (ws : source.globals.lookup (ofString "ws")=some (.val (.word heap)))
    (cell : source.locals.lookup (ofString name)=some (.val (.word word)))
    (mapped : source.memaddrs (heap+BitVec.ofNat 64 offset)) :
    evaluateHOLFiniteState source (store offset name)=(none,written source heap offset word) := by
  have addressRead : eval source (.op .add [.var .global (ofString "ws"),.const (BitVec.ofNat 64 offset)])=some (.val (.word (heap+BitVec.ofNat 64 offset))) := by
    simp [eval,evalHOLExact,evalListHOLExact,ws,valueIsWord,valueWord,wordOpHOL,wordOp]
  have valueRead : eval source (localVar name)=some (.val (.word word)) := by simp [eval,evalHOLExact,toExact,localVar,cell]
  exact StoreWord.execute source _ _ _ _ addressRead valueRead mapped

/-- The three real workspace stores are executed with their current local
values and actual mapped addresses, preserving the arbitrary later outcome. -/
theorem stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nodes root codes : BitVec 64)
    (ws : source.globals.lookup (ofString "ws")=some (.val (.word heap)))
    (nodesCell : source.locals.lookup (ofString "nodedb")=some (.val (.word nodes)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (codesCell : source.locals.lookup (ofString "codedb")=some (.val (.word codes)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 40) (aligned : heap.toNat%8=0) :
    evaluateHOLFiniteState source afterAllocation=
      evaluateHOLFiniteState (written (written (written source heap 0 nodes) heap 8 root) heap 16 codes) rootCall := by
  let one:=written source heap 0 nodes
  let two:=written one heap 8 root
  let three:=written two heap 16 codes
  have first:=store_execute source heap 0 "nodedb" nodes ws nodesCell (AllocatedBytes.word_mapped source heap 40 0 domain arena (by decide) aligned (by decide))
  have second:=store_execute one heap 8 "state_root" root ws rootCell (AllocatedBytes.word_mapped one heap 40 8 domain arena (by decide) aligned (by decide))
  have third:=store_execute two heap 16 "codedb" codes ws codesCell (AllocatedBytes.word_mapped two heap 40 16 domain arena (by decide) aligned (by decide))
  rw [shapes.2.1,StateSteps.next_sequence source one _ _ first (Nat.le_refl _),shapes.2.2.1,
    StateSteps.next_sequence one two _ _ second (Nat.le_refl _),shapes.2.2.2.1,
    StateSteps.next_sequence two three _ _ third (Nat.le_refl _)]

/-- The original prefix spends exactly its one allocation caller tick and
reaches the actual root materializer with the initialized40-byte workspace. -/
theorem execute_prefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap oldWs nodes root codes : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (ws : source.globals.lookup (ofString "ws")=some (.val (.word oldWs)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (nodesCell : source.locals.lookup (ofString "nodedb")=some (.val (.word nodes)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (codesCell : source.locals.lookup (ofString "codedb")=some (.val (.word codes)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 40) (aligned : heap.toNat%8=0) (room : heap.toNat+40≤2952790016) (funded : 1≤source.clock) :
    evaluateHOLFiniteState source body=evaluateHOLFiniteState (ready source heap nodes root codes) rootCall := by
  have alloc:=PersistentAlloc.global_call_execute source "ws" oldWs heap 40#64 ws [.const 40#64] rfl (PersistentAlloc.original_code source.code installed) heapCell room funded
  have newWs : (allocated source heap).globals.lookup (ofString "ws")=some (.val (.word heap)) := by
    simp [allocated,Input.putGlobal,HolFiniteMapExact.update,FUPDATE]
  have stores:=stores_execute (allocated source heap) heap nodes root codes newWs nodesCell rootCell codesCell domain arena aligned
  rw [shapes.1,StateSteps.next_sequence source (allocated source heap) allocate afterAllocation alloc (by change source.clock-1≤source.clock; omega),stores]
  rfl

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.store_execute
#print axioms InitECandidate.Solver.Mpt.StateInit.stores_execute
#print axioms InitECandidate.Solver.Mpt.StateInit.execute_prefix
