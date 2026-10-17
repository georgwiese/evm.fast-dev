import InitECandidate.Solver.WitnessRadix.SplitProgram
import InitECandidate.Solver.WitnessRadix.StoreWord

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace InitECandidate.Solver.WitnessRadix.SplitProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

structure Locals {F : Type} (source : PanSemStateFiniteExact 64 F)
    (node depth start count zeros bit dest pendingStart pendingCount pendingNode : BitVec 64) : Prop where
  nodeLocal : source.locals.lookup (ofString "node") = some (.val (.word node))
  nextLocal : source.locals.lookup (ofString "node_next") = some (.val (.word node))
  depthLocal : source.locals.lookup (ofString "depth") = some (.val (.word depth))
  startLocal : source.locals.lookup (ofString "start") = some (.val (.word start))
  countLocal : source.locals.lookup (ofString "count") = some (.val (.word count))
  zerosLocal : source.locals.lookup (ofString "zeros") = some (.val (.word zeros))
  bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word bit))
  destLocal : source.locals.lookup (ofString "dest") = some (.val (.word dest))
  pendingStartLocal : source.locals.lookup (ofString "pending_start") = some (.val (.word pendingStart))
  pendingCountLocal : source.locals.lookup (ofString "pending_count") = some (.val (.word pendingCount))
  pendingNodeLocal : source.locals.lookup (ofString "pending_node") = some (.val (.word pendingNode))

structure Mapped {F : Type} (source : PanSemStateFiniteExact 64 F)
    (node depth dest pendingStart pendingCount pendingNode : BitVec 64) : Prop where
  nodeMapped : source.memaddrs node
  zeroMapped : source.memaddrs (node + 8#64)
  oneMapped : source.memaddrs (node + 16#64)
  destMapped : source.memaddrs dest
  startMapped : source.memaddrs (pendingStart + depth * 8#64)
  countMapped : source.memaddrs (pendingCount + depth * 8#64)
  parentMapped : source.memaddrs (pendingNode + depth * 8#64)

def branchMemory (memory : BitVec 64 → HolWordLab 64)
    (node depth start count zeros bit dest pendingStart pendingCount pendingNode : BitVec 64) :
    BitVec 64 → HolWordLab 64 :=
  let a := StoreWord.put memory node bit
  let b := StoreWord.put a (node + 8#64) 0#64
  let c := StoreWord.put b (node + 16#64) 0#64
  let d := StoreWord.put c dest node
  let e := StoreWord.put d (pendingStart + depth * 8#64) (start + zeros)
  let f := StoreWord.put e (pendingCount + depth * 8#64) (count - zeros)
  StoreWord.put f (pendingNode + depth * 8#64) node

def branchPost {F : Type} (source : PanSemStateFiniteExact 64 F)
    (node depth start count zeros bit dest pendingStart pendingCount pendingNode : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  let written := ({ source with
    memory := branchMemory source.memory node depth start count zeros bit dest pendingStart pendingCount pendingNode });
  bind (bind (bind (bind (bind written "node_next" (node + 24#64)) "depth" (depth + 1#64))
    "count" zeros) "dest" (node + 8#64)) "bit" (bit + 1#64)

/-- Literal branch allocation and pending-right-task push. Seven mapped
word stores and five local assignments are exposed exactly; no clock is paid. -/
theorem body_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (node depth start count zeros bit dest pendingStart pendingCount pendingNode : BitVec 64)
    (locals : Locals source node depth start count zeros bit dest pendingStart pendingCount pendingNode)
    (mapped : Mapped source node depth dest pendingStart pendingCount pendingNode) :
    evaluateHOLFiniteState source allocationBody =
      (none, branchPost source node depth start count zeros bit dest pendingStart pendingCount pendingNode) := by
  classical
  rcases locals with ⟨nodeLocal, nextLocal, depthLocal, startLocal, countLocal, zerosLocal,
    bitLocal, destLocal, pendingStartLocal, pendingCountLocal, pendingNodeLocal⟩
  simp [ofString] at nodeLocal nextLocal depthLocal startLocal countLocal zerosLocal bitLocal destLocal pendingStartLocal pendingCountLocal pendingNodeLocal
  simp [allocationBody, allocationOps, sequence, assign, pendingAddress, localVar, addConst,
    evaluateHOLFiniteState_seq, evaluateHOLFiniteState_assign, evaluateHOLFiniteState_store,
    evalHOLExact, evalListHOLExact, toExact, isValidValueHOLFinite, lookupKvarHOLFinite,
    setKvarHOLFinite, setVarHOLFinite, QueryBranch.bind, HolFiniteMapExact.update, FUPDATE, ofString,
    nodeLocal, nextLocal, depthLocal, startLocal, countLocal, zerosLocal, bitLocal, destLocal,
    pendingStartLocal, pendingCountLocal, pendingNodeLocal, valueIsWord, valueWord,
    panOpHOL, wordOpHOL, wordOp, shapeOfHOLExact, shapeEqHOL, flattenHOL,
    panMemStoresHOL, panMemStoreHOL, mapped.nodeMapped, mapped.zeroMapped, mapped.oneMapped,
    mapped.destMapped, mapped.startMapped, mapped.countMapped, mapped.parentMapped,
    fixClockHOLFinite, branchPost, branchMemory, StoreWord.put]
  rfl

end InitECandidate.Solver.WitnessRadix.SplitProgram

#print axioms InitECandidate.Solver.WitnessRadix.SplitProgram.body_execute
