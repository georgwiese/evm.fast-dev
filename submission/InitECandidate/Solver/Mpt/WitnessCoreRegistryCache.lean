import InitECandidate.Solver.Mpt.WitnessCoreRegistryFrame

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Entering/restoring a real lexical scope retains the complete active
registry when its physical memory/domain and actual result cell agree. -/
theorem ActiveRegistry.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db : BitVec 64) (cfg : Configuration) (registry : ActiveRegistry source frontier db cfg)
    (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs)
    (result : target.locals.lookup (ofString "result")=source.locals.lookup (ofString "result")) :
    ∃ next : ActiveRegistry target frontier db cfg,next.nodes.graph.valid=registry.nodes.graph.valid := by
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=registry.nodes.graph.after_agreement source target 1024 frontier cfg.heap.toNat (WitnessValue db)
    registry.nodes.values registry.nodes.regions registry.nodes.disjoint domain (fun _ _=>congrFun memory _) (fun _ _=>congrFun memory _)
  let nodes : NodeRegistry target frontier cfg.heap db:=⟨graph,values,regions,disjoint⟩
  have includes : ∀ node,registry.nodes.graph.valid node → graph.valid node := by intro node member; rw [validEq]; exact member
  have children : ChildViews target graph.valid cfg.stack := by
    intro entry member
    have current:=registry.children entry member
    cases payload : entry.data.payload with
    | extension nibbles length=>simp only [ChildView,payload]
    | branch node index occupied=>
      simp only [ChildView,payload] at current ⊢
      exact ⟨(current.1.enlarge source registry.nodes.graph.valid graph.valid node index.val includes).frame source target graph.valid node index.val
        (fun _ _=>congrFun memory _),current.2.frame source target node (congrFun memory _) (congrFun memory _)⟩
  have tags : ∀ node,registry.nodes.graph.valid node → node≠0#64 → wordAt target.memory node=wordAt source.memory node := by
    intro node member active; rw [memory]
  have excluded:=registry.excludes_same source target frontier db cfg graph validEq tags
  refine ⟨⟨nodes,children,excluded,?_⟩,validEq⟩
  intro phase node cell
  rw [result] at cell
  exact includes node (registry.returned phase node cell)

/-- The actual pending hash cache preserves initialized child/value
fields in every active branch, all completed nodes and their exclusions. -/
theorem ActiveRegistry.after_cache (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap cursor child hash : BitVec 64) (entry : Entry) (rest : List Entry)
    (registry : ActiveRegistry source frontier db ⟨heap,cursor,entry::rest,.returning,true⟩)
    (view : View source db cursor.toNat heap.toNat (entry::rest))
    (owned : ResultOwned source entry.mark heap.toNat child) (member : registry.nodes.graph.valid child) :
    ∃ next : ActiveRegistry (returnCacheState source child hash) frontier db ⟨heap,cursor,entry::rest,.returning,true⟩,
      next.nodes.graph.valid=registry.nodes.graph.valid := by
  let target:=returnCacheState source child hash
  obtain ⟨nodes,validEq⟩:=registry.nodes.after_cache source frontier heap db child hash member
  have includes : ∀ node,registry.nodes.graph.valid node → nodes.graph.valid node := by intro node member; rw [validEq]; exact member
  have marks (current : Entry) (member : current∈entry::rest) : current.mark≤entry.mark := by
    rcases List.mem_cons.mp member with same|older
    · subst current; exact Nat.le_refl _
    · have order:=view.ordered.1 current older
      have before:=(view.before entry List.mem_cons_self).1
      omega
  have children : ChildViews target nodes.graph.valid (entry::rest) :=
    registry.children.frame source target registry.nodes.graph.valid nodes.graph.valid db cursor.toNat heap.toNat (entry::rest) view includes (by
      intro current member query lower upper
      exact cache_before source child hash entry.mark heap.toNat owned query (lt_of_lt_of_le upper (marks current member)))
  have tags : ∀ node,registry.nodes.graph.valid node → node≠0#64 → wordAt target.memory node=wordAt source.memory node := by
    intro node nodeMember active
    by_cases zero : child=0#64
    · dsimp only [target]; rw [returnCacheState,if_pos (Or.inr zero)]
    · have away : node≠child+24#64 := by
        have bound:=TrieWalk.nodeBytes_bounds (wordAt source.memory node)
        simpa only [byteAddress,BitVec.add_zero] using registry.nodes.graph.cache_away frontier heap.toNat registry.nodes.regions registry.nodes.disjoint
          child node 0 member zero nodeMember active (by omega) (by decide)
      unfold wordAt
      rw [return_cache_memory source child hash node away]
  have excluded:=registry.excludes_same source target frontier db _ nodes.graph validEq tags
  refine ⟨⟨nodes,children,excluded,?_⟩,validEq⟩
  intro phase node cell
  have locals : target.locals=source.locals := by unfold target returnCacheState; split <;> rfl
  rw [locals] at cell
  exact includes node (registry.returned phase node cell)

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.of_fields
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.after_cache
