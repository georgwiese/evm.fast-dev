import InitECandidate.Solver.Mpt.DeleteDescentBranchProgram
import InitECandidate.Solver.Mpt.BranchValueUpdateGraph
import InitECandidate.Solver.Mpt.TriePathBufferMutation
import InitECandidate.Solver.Mpt.TriePathFieldsMutation
import InitECandidate.Solver.Mpt.LocalFieldStores

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Execute the original two constant-zero branch-value stores before
the actual collapse call. Both addresses are initialized mapped fields. -/
theorem branch_clear_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=3#64) :
    evaluateHOLFiniteState source branchClear=evaluateHOLFiniteState (BranchValueUpdate.post source model.node 0#64 0#64) branchCollapse := by
  let view:=model.pending.values.branch model.node model.nodeMember active (by rw [tag]; decide) (by rw [tag]; decide) (by rw [tag]; decide)
  let fields : List LocalFields.Field:=[⟨160,.literal 0#64⟩,⟨168,.literal 0#64⟩]
  have ready : ∀ field∈fields,field.value.Ready source:=by
    intro field member
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> trivial
  have mapped : ∀ field∈fields,source.memaddrs (model.node+BitVec.ofNat 64 field.offset):=by
    intro field member
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact view.pointerMapped
    · exact view.lengthMapped
  exact LocalFields.execute source "node" model.node fields model.nodeCell ready mapped branchCollapse

/-- Genuine zero-value writes retain all graph/path/query and saved
parent facts. The empty-value predicate is a current payload property,
independent of any future helper success. -/
theorem branch_clear_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=3#64) (empty : property 0#64 0#64) :
    let post:=BranchValueUpdate.post source model.node 0#64 0#64
    ∃ next : TrieWalk.Graph post.memory post.memaddrs,next.valid=model.pending.graph.valid ∧
      next.Regions nodeLower model.pending.heap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
      next.PathBytes post.be ∧ next.PathRegions pathLower model.pending.heap.toNat ∧ next.PathSeparated ∧
      next.PathBuffer post.be pathLower model.pending.heap.toNat key length.toNat ∧
      model.pending.graph.PathFields post.memory ∧
      ∀ query : BitVec 64,query.toNat<nodeLower→post.memory query=source.memory query := by
  let post:=BranchValueUpdate.post source model.node 0#64 0#64
  have notHash : wordAt source.memory model.node≠0#64:=by rw [tag]; decide
  have notLeaf : wordAt source.memory model.node≠1#64:=by rw [tag]; decide
  have notExtension : wordAt source.memory model.node≠2#64:=by rw [tag]; decide
  have payload : TrieWalk.Payload source.memaddrs 0#64 0#64 limit:=by
    constructor
    · exact Nat.zero_le _
    constructor
    · decide
    · intro offset inside; simp at inside
  obtain ⟨next,same,regions,disjoint,values,paths,pathRegions,separated⟩:=model.pending.graph.after_branch_value_update source model.node 0#64 0#64
    limit nodeLower model.pending.heap.toNat pathLower model.pending.heap.toNat property model.pending.values model.pending.regions model.pending.disjoint
      model.pending.paths model.pending.pathRegions model.pending.separated model.nodeMember active notHash notLeaf notExtension payload empty
  have buffer:=model.query.after_branch_value_update source model.pending.graph nodeLower model.pending.heap.toNat pathLower model.pending.heap.toNat key length.toNat
    model.pending.regions model.pending.disjoint model.node 0#64 0#64 model.nodeMember active notHash notLeaf notExtension next same
  have fields:=TrieWalk.Graph.PathFields.of_branch_value source model.node 0#64 0#64 model.pending.graph nodeLower model.pending.heap.toNat
    model.pending.regions model.pending.disjoint model.nodeMember active notHash notLeaf notExtension
  have bounds:=model.pending.regions model.node model.nodeMember active
  have nodeSize : TrieWalk.nodeBytes (wordAt source.memory model.node)=176:=by rw [tag]; rfl
  have low (query : BitVec 64) (before : query.toNat<nodeLower) : post.memory query=source.memory query:=by
    have away (offset : Nat) (inside : offset<176) : query≠byteAddress model.node offset:=by
      intro equal
      have number:=congrArg BitVec.toNat equal
      rw [byteAddress_toNat model.node offset (by have upper:=bounds.2.1.upper; rw [nodeSize] at upper; omega)] at number
      omega
    exact BranchValueUpdate.post_away source model.node 0#64 0#64 query (away 160 (by decide)) (away 168 (by decide))
  exact ⟨next,same,regions,disjoint,values,paths,pathRegions,separated,buffer,fields,low⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_clear_execute
#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_clear_memory
