import InitECandidate.Solver.Mpt.WitnessCoreRegistryFrame

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- The real return path protects the whole older-record band. Its
older persistent branch payloads lie in that same protected band. -/
theorem ChildViews.return_tail (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first second : BitVec 64 → Prop) (db : BitVec 64) (cursor heap : Nat) (entry : Entry) (rest : List Entry)
    (view : View source db cursor heap (entry::rest)) (children : ChildViews source first (entry::rest))
    (includes : ∀ child,first child → second child)
    (memory : ∀ query : BitVec 64,entry.record.toNat+88≤query.toNat → query.toNat<entry.data.payload.startAddress → target.memory query=source.memory query) :
    ChildViews target second rest := by
  apply (children.tail source first entry rest).frame source target first second db cursor heap rest (view.tail source db cursor heap entry rest) includes
  intro parent member query lower upper
  have parentFloor:=(view.records parent (List.mem_cons_of_mem entry member)).payloadFloor
  have recordCeiling:=(view.records entry List.mem_cons_self).ceiling
  have parentBefore:=(view.ordered.1 parent member).2.2
  exact memory query (by omega) (by omega)

/-- A popped parent result follows the old head's payload floor. Every
older pending branch ends before that floor, even when the completed
result was allocated before some of its already registered children. -/
theorem ActiveRegistry.tail_excludes_extension (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap cursor : BitVec 64) (entry : Entry) (rest : List Entry)
    (registry : ActiveRegistry source frontier db ⟨heap,cursor,entry::rest,.returning,true⟩)
    (view : View source db cursor.toNat heap.toNat (entry::rest))
    (next : TrieWalk.Graph target.memory target.memaddrs) (result : BitVec 64)
    (members : ∀ node,next.valid node → registry.nodes.graph.valid node ∨ node=result)
    (tags : ∀ node,registry.nodes.graph.valid node → node≠0#64 → wordAt target.memory node=wordAt source.memory node)
    (fresh : result≠0#64 → entry.data.payload.startAddress≤result.toNat) :
    ∀ parent∈rest,∀ node index occupied,parent.data.payload=.branch node index occupied → next.Excludes node 176 := by
  intro parent member node index occupied payload
  have before:=(view.before parent (List.mem_cons_of_mem entry member)).2
  have order:=(view.ordered.1 parent member).2.2
  have nodeBefore : node.toNat+176≤entry.data.payload.startAddress := by
    simp only [payload,WitnessRecord.Payload.endAddress] at before
    omega
  exact (registry.excludes parent (List.mem_cons_of_mem entry member) node index occupied payload).after_extension
    source.memory target.memory source.memaddrs target.memaddrs registry.nodes.graph next node result 176 members tags (fun active=>nodeBefore.trans (fresh active))

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ChildViews.return_tail
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.tail_excludes_extension
