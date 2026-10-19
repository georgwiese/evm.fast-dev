import InitECandidate.Solver.Mpt.TrieWalkLeaf
import InitECandidate.Solver.Mpt.TrieWalkEffects
import InitECandidate.Solver.Mpt.TrieWalkValues
import InitECandidate.Solver.Input.ReturnFactsScoped

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open Input.ReturnFacts

variable {property : BitVec 64 → BitVec 64 → Prop}

def leafFound : ProgHOL 64 := .return (.rstruct [.const 1#64,nodeField 48#64,nodeField 56#64])

set_option maxRecDepth 10000 in
theorem leaf_match_shape : leafMatch=.ite (.cmp .notEqual (localVar "eq") (.const 0#64)) leafFound .skip := by
  simp only [leafMatch,leafCompare,leafLengthGuard,leafAfterSize,leaf,leafGuard,afterHash,afterK,loopBody,loop,afterPos,body,
    Guest.guestFn_trie_walk,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,leafFound,nodeField,addConst,localVar]

theorem absent_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (domain : BitVec 64 → Prop) (limit : Nat) :
    Returns source absent (Answer domain limit (property:=property)) := by
  apply Input.ReturnFacts.returned source _ (triple 0#64 0#64 0#64)
    (Answer domain limit (property:=property)) _ (Answer.absent (property:=property) domain limit)
  simp [eval,evalHOLExact,evalListHOLExact,triple]

theorem leaf_found_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (view : ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) :
    Returns source leafFound (Answer source.memaddrs limit (property:=property)) := by
  classical
  have pointerRead := node_field_read source node 48#64 view.pointer nodeCell view.pointerMapped view.pointerStored
  have lengthRead := node_field_read source node 56#64 view.length nodeCell view.lengthMapped view.lengthStored
  apply Input.ReturnFacts.returned source _ (triple 1#64 view.pointer view.length)
    (Answer source.memaddrs limit (property:=property)) _ (view.answer _ _ _ _ _ _)
  simp only [eval] at pointerRead lengthRead ⊢
  change evalHOLExact source.toExact (.rstruct [.const 1#64,nodeField 48#64,nodeField 56#64])=_
  simp only [evalHOLExact,evalListHOLExact]
  rw [pointerRead,lengthRead]
  rfl

theorem leaf_match_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (view : ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) :
    Returns source leafMatch (Answer source.memaddrs limit (property:=property)) := by
  rw [leaf_match_shape]
  exact Input.ReturnFacts.conditional source _ _ _ _ (leaf_found_returns source node limit view nodeCell) (Input.ReturnFacts.skip source _)

theorem leaf_compare_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (view : ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (installed : Input.OriginalCode.Installed source.code) :
    Returns source leafCompare (Answer source.memaddrs limit (property:=property)) := by
  rw [leaf_compare_shape]
  apply Input.ReturnFacts.scoped_readonly source "eq" .one (ofString "memeq") leafArguments Memeq32.formals Memeq32.body leafMatch .one
    (memeq_code source.code installed) (memeq_readonly source.code)
  intro target returned fields
  let ready := Input.CallNormal.continuationEntry source target "eq" returned
  have memory := Input.LocalEffects.memory_of_erase source target fields
  have domain := congrArg PanSemStateFiniteExact.memaddrs fields
  change target.memaddrs=source.memaddrs at domain
  have nextView : ValueView ready.memory ready.memaddrs node 48#64 56#64 limit property := by
    change ValueView target.memory target.memaddrs node 48#64 56#64 limit property
    rw [memory,domain]
    exact view
  have currentNode : ready.locals.lookup (ofString "node")=some (.val (.word node)) := by
    simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,nodeCell,
      show ofString "eq"≠ofString "node" from by decide]
  have result := leaf_match_returns ready node limit nextView currentNode
  change Returns ready leafMatch (Answer target.memaddrs limit (property:=property)) at result
  rwa [domain] at result

/-- Every real normal leaf return is absent or carries the current actual
typed value pointer/length and its bounded mapped payload. -/
theorem leaf_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (view : ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (installed : Input.OriginalCode.Installed source.code) :
    Returns source leaf (Answer source.memaddrs limit (property:=property)) := by
  rw [leaf_body_shape]
  apply Input.ReturnFacts.declared
  intro value
  let entered := setVarHOLFinite (ofString "rl") value source
  have currentNode : entered.locals.lookup (ofString "node")=some (.val (.word node)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,nodeCell,
      show ofString "rl"≠ofString "node" from by decide]
  apply Input.ReturnFacts.sequence
  · rw [leaf_length_shape]
    exact Input.ReturnFacts.conditional entered _ _ _ _ (leaf_compare_returns entered node limit view currentNode installed) (Input.ReturnFacts.skip entered _)
  · intro middle normal
    exact absent_returns middle source.memaddrs limit

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.leaf_match_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.absent_returns
#print axioms InitECandidate.Solver.Mpt.TrieWalk.leaf_found_returns
#print axioms InitECandidate.Solver.Mpt.TrieWalk.leaf_match_returns
#print axioms InitECandidate.Solver.Mpt.TrieWalk.leaf_compare_returns
#print axioms InitECandidate.Solver.Mpt.TrieWalk.leaf_returns
