import InitECandidate.Solver.Mpt.SetMutationCost
import InitECandidate.Solver.Mpt.InsertAssignedPaths

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- The common physical result of the original setter's actual deletion
or insertion caller. Headers may lie between old and fresh trie nodes. -/
structure MutationOutput (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (incoming key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop) where
  root : BitVec 64
  heap : BitVec 64
  locals : target.locals=source.locals.update (ofString "root",.val (.word root))
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  code : target.code=source.code
  globalsNonHeap : HeapGlobals source target
  price : source.clock-target.clock≤mutationAllowance pathLower
  heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapAligned : heap.toNat%8=0
  grows : incoming.toNat≤heap.toNat
  fields : graph.PathFields target.memory
  next : TrieWalk.Graph target.memory target.memaddrs
  members : ∀ node,graph.valid node→next.valid node
  freshMembers : ∀ node,next.valid node→graph.valid node ∨ incoming.toNat≤node.toNat
  rootMember : next.valid root
  regions : next.Regions nodeLower heap.toNat
  disjoint : next.Disjoint
  values : TrieWalk.Values next limit property
  paths : next.PathBytes target.be
  pathRegions : next.PathRegions pathLower heap.toNat
  separated : next.PathSeparated
  protectedWords : ∀ address : BitVec 64,graph.ProtectedWord address →
    DeleteFrame.ceiling≤address.toNat → address.toNat<incoming.toNat →
    TrieWalk.PathWordAway key length.toNat address →
    target.memory address=source.memory address ∧ next.ProtectedWord address

/-- Derive both genuine original mutation calls and their common output
from the actual branch condition. Payload ownership is required only for
a currently nonzero pointer and length, so deletion at zero needs none. -/
theorem mutation_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor frame root key length pointer size : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (valuesModel : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid root)
    (small : length.toNat≤64) (empty : property 0#64 0#64)
    (owned : pointer≠0#64→size≠0#64→TrieWalk.Payload source.memaddrs pointer size limit ∧ property pointer size)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root)))
    (nkCell : source.locals.lookup (ofString "nk")=some (.rStruct [.val (.word key),.val (.word length)]))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (scratch : Rlp.Validation.Arena source cursor frame) (scratchBefore : cursor.toNat≤DeleteFrame.ceiling)
    (floor : DeleteFrame.ceiling≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source mutationChoice=(none,target)) :
    Nonempty (MutationOutput source target graph heap key length limit nodeLower pathLower property) := by
  have price:=mutation_cost source heap cursor frame root key length pointer size graph limit nodeLower pathLower property valuesModel regions disjoint paths pathRegions separated query member
    small empty owned rootCell nkCell pointerCell sizeCell heapCell heapArena heapAligned scratch scratchBefore floor pathFloor nodeFloor little installed
  rw [normal] at price
  rw [mutation_dispatch source pointer size pointerCell sizeCell] at normal
  by_cases absent : pointer=0#64 ∨ size=0#64
  · rw [if_pos absent,deletion_shape] at normal
    obtain ⟨returned,localsEq,⟨output⟩⟩:=DeleteNode.assigned_normal source target heap cursor frame root key length 0#64 graph limit nodeLower pathLower property
      valuesModel regions disjoint paths pathRegions separated query member small (by simp) empty heapCell heapArena heapAligned scratch scratchBefore floor pathFloor nodeFloor little installed
      (ofString "root") deleteArguments (delete_arguments source root key length rootCell nkCell) normal
    exact ⟨{
      root:=output.root
      heap:=output.finalHeap
      locals:=by rw [output.answer] at localsEq; exact localsEq
      domain:=output.domain
      endian:=output.endian
      code:=output.code
      globalsNonHeap:=output.globalsNonHeap
      price:=price
      heapCell:=output.heapCell
      heapArena:=output.heapArena
      heapAligned:=output.heapAligned
      grows:=output.grows
      fields:=output.fields
      next:=output.next
      members:=output.members
      freshMembers:=output.freshMembers
      rootMember:=output.rootMember
      regions:=output.regions
      disjoint:=output.disjoint
      values:=output.values
      paths:=output.paths
      pathRegions:=output.pathRegions
      separated:=output.separated
      protectedWords:=by intro address safe above before _away; exact output.protectedWords address safe above before }⟩
  · rw [if_neg absent] at normal
    obtain ⟨payload,extra⟩:=owned (fun zero=>absent (Or.inl zero)) (fun zero=>absent (Or.inr zero))
    obtain ⟨answer,localsEq,⟨output⟩⟩:=Insert.assigned_path_normal source target heap root key 0#64 length pointer size graph limit nodeLower pathLower property
      valuesModel regions disjoint paths pathRegions separated query member (by simp) small payload extra empty nodeFloor scratch.domain installed heapCell heapArena heapAligned
      (ofString "root") insertArguments (insert_arguments source root key length pointer size rootCell nkCell pointerCell sizeCell) normal
    exact ⟨{
      root:=answer
      heap:=output.heap
      locals:=localsEq
      domain:=output.domain
      endian:=output.endian
      code:=output.code
      globalsNonHeap:=output.globalsNonHeap
      price:=price
      heapCell:=output.heapCell
      heapArena:=output.heapArena
      heapAligned:=output.heapAligned
      grows:=output.heapGrows
      fields:=output.oldPathFields
      next:=output.next
      members:=output.members
      freshMembers:=output.freshMembers
      rootMember:=output.rootMember
      regions:=output.regions
      disjoint:=output.disjoint
      values:=output.values
      paths:=output.paths
      pathRegions:=output.pathRegions
      separated:=output.separated
      protectedWords:=by
        intro address safe _above before away
        exact ⟨output.protectedMemory address safe before,output.protectedGraph address safe before away⟩ }⟩

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.mutation_normal
