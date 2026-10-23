import InitECandidate.Solver.Mpt.DeleteNodeBodyCall
import InitECandidate.Solver.Mpt.DeleteNodeSetup

namespace InitECandidate.Solver.Mpt.DeleteNode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_mark_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor frame node key length level : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid node)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (small : length.toNat≤64) (within : level.toNat≤length.toNat) (empty : property 0#64 0#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (scratch : Rlp.Validation.Arena source cursor frame) (scratchBefore : cursor.toNat≤DeleteFrame.ceiling)
    (floor : DeleteFrame.ceiling≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterMark).2.clock≤DeleteBody.bodyAllowance pathLower+3 := by
  let ready:=scalarSetup source
  have readyNode : ready.locals.lookup (ofString "node")=some (.val (.word node)):=(scalar_saved source "node" (by decide) (by decide)).trans nodeCell
  have readyKey : ready.locals.lookup (ofString "key")=some (.val (.word key)):=(scalar_saved source "key" (by decide) (by decide)).trans keyCell
  have readyLength : ready.locals.lookup (ofString "klen")=some (.val (.word length)):=(scalar_saved source "klen" (by decide) (by decide)).trans lengthCell
  have readyLevel : ready.locals.lookup (ofString "level")=some (.val (.word level)):=(scalar_saved source "level" (by decide) (by decide)).trans levelCell
  have readyScratch:=scratch.of_fields source ready cursor frame rfl rfl
  have called:=caught_body_cost ready heap cursor frame node key length level graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated query member
    readyNode readyKey readyLength readyLevel small within empty heapCell heapArena heapAligned readyScratch scratchBefore floor pathFloor nodeFloor little installed
  have afterPrice : Input.ClockCost.Bound source.code afterCall 1:=by
    rw [shapes.2.2.2.2.1]
    exact Input.ClockCost.sequence source.code _ _ 1 0 (Arenas.Scratch.release_call_price source.code installed releaseArguments) (Input.ClockCost.returned source.code (localVar "res"))
  have corePrice:=Input.ClockCost.sequence_current ready caughtCall afterCall (DeleteBody.bodyAllowance pathLower+2) 1 called afterPrice
  rw [shapes.2.1]
  apply Input.ClockCost.declared_current source "e" (.const 0#64) 0#64 afterError _ rfl
  rw [shapes.2.2.1]
  apply Input.ClockCost.declared_current (QueryBranch.bind source "e" 0#64) "res" (.const 0#64) 0#64 afterResult _ rfl
  rw [shapes.2.2.2.1]
  exact corePrice

/-- All outcomes of the whole unchanged255 wrapper, including a caught
MptErr release/rethrow and allocation failures/timeouts in original254.
The real mark, body caller, handler and final release add at most4 local
source ticks to the checked body allowance. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor frame node key length level : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid node)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (small : length.toNat≤64) (within : level.toNat≤length.toNat) (empty : property 0#64 0#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (scratch : Rlp.Validation.Arena source cursor frame) (scratchBefore : cursor.toNat≤DeleteFrame.ceiling)
    (floor : DeleteFrame.ceiling≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤DeleteBody.bodyAllowance pathLower+4 := by
  by_cases zero : source.clock=0
  · simp only [zero,Nat.zero_sub,Nat.zero_le]
  · let current:=marked source cursor
    have currentNode : current.locals.lookup (ofString "node")=some (.val (.word node)):=(mark_saved source cursor "node" (by decide)).trans nodeCell
    have currentKey : current.locals.lookup (ofString "key")=some (.val (.word key)):=(mark_saved source cursor "key" (by decide)).trans keyCell
    have currentLength : current.locals.lookup (ofString "klen")=some (.val (.word length)):=(mark_saved source cursor "klen" (by decide)).trans lengthCell
    have currentLevel : current.locals.lookup (ofString "level")=some (.val (.word level)):=(mark_saved source cursor "level" (by decide)).trans levelCell
    have currentScratch:=scratch.of_fields source current cursor frame rfl rfl
    have priced:=after_mark_cost current heap cursor frame node key length level graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated query member
      currentNode currentKey currentLength currentLevel small within empty heapCell heapArena heapAligned currentScratch scratchBefore floor pathFloor nodeFloor little installed
    have actual:=Arenas.mark_call source .down "mark" cursor afterMark (Arenas.Scratch.mark_code source.code installed) scratch.cursorGlobal (by omega)
    simp only [Arenas.markName] at actual
    rw [shapes.1,actual]
    change source.clock-(evaluateHOLFiniteState current afterMark).2.clock≤DeleteBody.bodyAllowance pathLower+4
    change source.clock-1-(evaluateHOLFiniteState current afterMark).2.clock≤DeleteBody.bodyAllowance pathLower+3 at priced
    omega

end InitECandidate.Solver.Mpt.DeleteNode

#print axioms InitECandidate.Solver.Mpt.DeleteNode.after_mark_cost
#print axioms InitECandidate.Solver.Mpt.DeleteNode.body_cost
