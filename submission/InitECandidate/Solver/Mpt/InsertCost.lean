import InitECandidate.Solver.Mpt.InsertLoopCost
import InitECandidate.Solver.Mpt.InsertLoopModelInitial

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual three scalar declarations always reach the initialized
loop remainder; their lexical restoration does not spend source clocks. -/
theorem setup_execution (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Input.CallPrefix.Execution source actions (setup source) := by
  exact .step (.declare source (ofString "result") .one (.const 0#64) (.val (.word 0#64)) rfl (by simp [shapeEqHOL,shapeOfHOLExact]))
    (.step (.declare _ (ofString "slot") .one (.const 0#64) (.val (.word 0#64)) rfl (by simp [shapeEqHOL,shapeOfHOLExact]))
      (.step (.declare _ (ofString "go") .one (.const 1#64) (.val (.word 1#64)) rfl (by simp [shapeEqHOL,shapeOfHOLExact])) (.done _)))

/-- Every outcome of whole unchanged251, including malformed reads,
collisions, allocation failures and short clocks, within36790 source
call/loop clocks. This local allowance is separate from target work. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key level length pointer size : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid node)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (before : level.toNat≤length.toNat) (bounded : length.toNat≤64)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size) (empty : property 0#64 0#64) (floor : nodeLower≤heap.toNat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤36790 := by
  obtain ⟨initial,_members,_heap⟩:=initial_loop_model source heap node key level length pointer size graph limit nodeLower pathLower property
    values regions disjoint paths pathRegions separated query member nodeCell keyCell levelCell lengthCell pointerCell sizeCell before bounded payload floor domain installed heapCell frontier aligned
  have loopPrice:=loop_cost (setup source) key length pointer size limit nodeLower pathLower property initial extra empty
  have price:=Input.ClockCost.sequence_current (setup source) (.while test loopBody) (.return (localVar "result")) 36790 0 loopPrice
    (Input.ClockCost.returned source.code (localVar "result"))
  have clocks:=congrArg Prod.snd ((setup_execution source).project loopAndAfter)
  change (evaluateHOLFiniteState source (Input.CallPrefix.program actions loopAndAfter)).2.clock=(evaluateHOLFiniteState (setup source) loopAndAfter).2.clock at clocks
  rw [←body_shape] at clocks
  rw [clocks,loop_shape]
  exact price

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.setup_execution
#print axioms InitECandidate.Solver.Mpt.Insert.body_cost
