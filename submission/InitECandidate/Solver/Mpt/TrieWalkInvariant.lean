import InitECandidate.Solver.Mpt.TrieWalkMemory

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def localWord (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) : BitVec 64 :=
  match source.locals.lookup (ofString name) with | some (.val (.word word)) => word | _ => 0#64

def currentRank (limit : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat :=
  Rank.value limit source.memory (localWord source "node") (localWord source "pos")

def Invariant (memory : Memory) (domain : BitVec 64 → Prop) (be : Bool) (valid : BitVec 64 → Prop)
    (nibs : BitVec 64) (limit : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  source.memory = memory ∧ source.memaddrs = domain ∧ source.be = be ∧
  source.locals.lookup (ofString "nibs") = some (.val (.word nibs)) ∧
  source.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))) ∧
  ∃ node position, valid node ∧ position.toNat ≤ limit ∧
    source.locals.lookup (ofString "node") = some (.val (.word node)) ∧
    source.locals.lookup (ofString "pos") = some (.val (.word position))

def Graph.rebase (memory memory' : Memory) (domain domain' : BitVec 64 → Prop)
    (graph : Graph memory domain) (sameMemory : memory' = memory) (sameDomain : domain' = domain) : Graph memory' domain' := by
  rw [sameMemory, sameDomain]
  exact graph

theorem Graph.rebase_valid (memory memory' : Memory) (domain domain' : BitVec 64 → Prop)
    (graph : Graph memory domain) (sameMemory : memory' = memory) (sameDomain : domain' = domain) :
    (Graph.rebase memory memory' domain domain' graph sameMemory sameDomain).valid = graph.valid := by
  subst memory'
  subst domain'
  rfl

theorem current_rank_eq (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node position : BitVec 64) (limit : Nat)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position))) :
    currentRank limit source = Rank.value limit source.memory node position := by
  simp only [currentRank, localWord, nodeCell, posCell]

theorem current_rank_upper (source : PanSemStateFiniteExact 64 Guest.HostMemory) (limit : Nat) :
    currentRank limit source ≤ 2 * limit + 2 := Rank.upper _ _ _ _

theorem condition_active (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node word : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (observed : evalHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) condition = some (.val (.word word)))
    (nonzero : word ≠ 0#64) : node ≠ 0#64 := by
  intro zero
  have read : evalHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) condition = some (.val (.word 0#64)) := by
    simp [condition, evalHOLFinite, evalHOLExact, localVar, toExact, nodeCell, zero,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have equal : 0#64 = word := by
    simpa only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using read.symm.trans observed
  exact nonzero equal.symm

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.rebase_valid
#print axioms InitECandidate.Solver.Mpt.TrieWalk.current_rank_eq
#print axioms InitECandidate.Solver.Mpt.TrieWalk.current_rank_upper
#print axioms InitECandidate.Solver.Mpt.TrieWalk.condition_active
