import InitECandidate.Solver.Mpt.TrieWalkLeafValues
import InitECandidate.Solver.Mpt.TrieWalkBranch
import InitECandidate.Solver.Input.ReturnFactsScalar

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open Input.ReturnFacts

def branchValueGuard : ProgHOL 64 := .ite (.cmp .equal (localVar "vl") (.const 0#64)) absent .skip
def branchFound : ProgHOL 64 := .return (.rstruct [.const 1#64,nodeField 160#64,localVar "vl"])

set_option maxRecDepth 10000 in
theorem branch_terminal_shape : branchTerminal=.dec (ofString "vl") .one (nodeField 168#64) (.seq branchValueGuard branchFound) := by
  simp only [branchTerminal,branchGuard,branch,nodeStep,afterHash,afterK,loopBody,loop,afterPos,body,
    Guest.guestFn_trie_walk,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,branchValueGuard,branchFound,absent,nodeField,addConst,localVar]

theorem branch_found_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (view : ValueView source.memory source.memaddrs node 160#64 168#64 limit)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (lengthCell : source.locals.lookup (ofString "vl")=some (.val (.word view.length))) :
    Returns source branchFound (Answer source.memaddrs limit) := by
  classical
  have pointerRead := node_field_read source node 160#64 view.pointer nodeCell view.pointerMapped view.pointerStored
  apply Input.ReturnFacts.returned source _ (triple 1#64 view.pointer view.length) _ _ (view.answer _ _ _ _ _ _)
  simp only [eval] at pointerRead ⊢
  change evalHOLExact source.toExact (.rstruct [.const 1#64,nodeField 160#64,localVar "vl"])=_
  simp only [evalHOLExact,evalListHOLExact]
  rw [pointerRead]
  simp [localVar,evalHOLExact,toExact,lengthCell,triple]

theorem branch_terminal_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (view : ValueView source.memory source.memaddrs node 160#64 168#64 limit)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) :
    Returns source branchTerminal (Answer source.memaddrs limit) := by
  have lengthRead := node_field_read source node 168#64 view.length nodeCell view.lengthMapped view.lengthStored
  rw [branch_terminal_shape]
  refine Input.ReturnFacts.declared_word source "vl" (nodeField 168#64) view.length (.seq branchValueGuard branchFound)
    (Answer source.memaddrs limit) lengthRead ?_
  let entered := bind source "vl" view.length
  have currentNode : entered.locals.lookup (ofString "node")=some (.val (.word node)) :=
    (bind_lookup_other source "vl" "node" view.length (by decide)).trans nodeCell
  have currentLength : entered.locals.lookup (ofString "vl")=some (.val (.word view.length)) := bind_lookup_same _ _ _
  apply Input.ReturnFacts.sequence
  · exact Input.ReturnFacts.conditional entered _ _ _ _ (absent_returns entered source.memaddrs limit) (Input.ReturnFacts.skip entered _)
  · intro middle normal
    have actual : evaluateHOLFiniteState entered branchValueGuard=
        if view.length=0#64 then evaluateHOLFiniteState entered absent else (none,entered) := by
      simp [branchValueGuard,evaluateHOLFiniteState_ite,evalHOLExact,toExact,localVar,currentLength,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    rw [actual] at normal
    by_cases zero : view.length=0#64
    · rw [if_pos zero] at normal
      exact (Input.NoFallthrough.returned _ entered (congrArg Prod.fst normal)).elim
    · rw [if_neg zero] at normal
      have middleEq := (congrArg Prod.snd normal).symm
      change middle=entered at middleEq
      subst middle
      exact branch_found_returns entered node limit view currentNode currentLength

theorem branch_advance_prefix : Input.LocalPrefix (ofString "nibs") branchAdvance := by
  rw [branch_advance_shape]
  have nodeSafe : Input.LocalPrefix (ofString "nibs") branchNode := by
    simp only [branchNode,branchAdvance,branch,nodeStep,afterHash,afterK,loopBody,loop,afterPos,body,
      Guest.guestFn_trie_walk,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
    exact .assign _ _ (by decide)
  exact .seq nodeSafe (.assign _ _ (by decide))

theorem branch_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (view : ValueView source.memory source.memaddrs node 160#64 168#64 limit)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) :
    Returns source branch (Answer source.memaddrs limit) := by
  rw [branch_shape]
  apply Input.ReturnFacts.sequence
  · rw [branch_guard_shape]
    exact Input.ReturnFacts.conditional source _ _ _ _ (branch_terminal_returns source node limit view nodeCell) (Input.ReturnFacts.skip source _)
  · intro middle normal
    exact Input.ReturnFacts.local_prefix middle (ofString "nibs") branchAdvance branch_advance_prefix _

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.branch_terminal_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.branch_found_returns
#print axioms InitECandidate.Solver.Mpt.TrieWalk.branch_terminal_returns
#print axioms InitECandidate.Solver.Mpt.TrieWalk.branch_advance_prefix
#print axioms InitECandidate.Solver.Mpt.TrieWalk.branch_returns
