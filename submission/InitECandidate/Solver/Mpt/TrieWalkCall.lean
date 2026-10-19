import InitECandidate.Solver.Mpt.TrieWalkCost
import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def values (node nibs : BitVec 64) (length : Nat) : List (ValueHOL 64) :=
  [.val (.word node), .val (.word nibs), .val (.word (BitVec.ofNat 64 length))]
def rawLocals (node nibs : BitVec 64) (length : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "nlen" then some (.val (.word (BitVec.ofNat 64 length))) else
  if name = ofString "nibs" then some (.val (.word nibs)) else
  if name = ofString "node" then some (.val (.word node)) else none

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (node nibs : BitVec 64) (length : Nat) (known : table (ofString "trie_walk") = some (formals, body, resultShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "trie_walk") (values node nibs length) = some (body, callee, resultShape) ∧
      callee.lookup (ofString "node") = some (.val (.word node)) ∧ callee.lookup (ofString "nibs") = some (.val (.word nibs)) ∧
      callee.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 length))) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values node nibs length).length ∧
      ((formals.zip (values node nibs length)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact table (ofString "trie_walk") (values node nibs length) = some (body, rawLocals node nibs length, resultShape) := by
    simp only [lookupCodeHOLExact, known, valid]
    rfl
  obtain ⟨callee, called, locals⟩ := CodeEnvironment.finite_lookup table
    (ofString "trie_walk") (values node nibs length) body (rawLocals node nibs length) resultShape raw
  refine ⟨callee, called, ?_, ?_, ?_⟩
  · rw [locals]
    simp [rawLocals, show ofString "node" ≠ ofString "nibs" from by decide, show ofString "node" ≠ ofString "nlen" from by decide]
  · rw [locals]
    simp [rawLocals, show ofString "nibs" ≠ ofString "nlen" from by decide]
  · rw [locals]
    simp [rawLocals]

theorem Graph.call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (node nibs : BitVec 64) (length : Nat)
    (key : KeyView source.memory source.memaddrs source.be nibs length) (member : graph.valid node)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values node nibs length))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock - (evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "trie_walk") arguments)).2.clock ≤ 2081 := by
  obtain ⟨callee, called, nodeLocal, nibsLocal, lengthLocal⟩ := environment source.code.lookup node nibs length (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have cost := Graph.body_cost entry graph node nibs length key member nodeLocal nibsLocal lengthLocal installed
  exact Input.ClockCost.call_current source destination (ofString "trie_walk") arguments _ body callee resultShape 2080 args called cost

theorem Graph.scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (node nibs : BitVec 64) (length : Nat)
    (key : KeyView source.memory source.memaddrs source.be nibs length) (member : graph.valid node)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (continuationPrice : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values node nibs length))
    (installed : Input.OriginalCode.Installed source.code)
    (priced : Input.ClockCost.Bound source.code continuation continuationPrice) :
    source.clock - (evaluateHOLFiniteState source (.decCall name resultShape (ofString "trie_walk") arguments continuation)).2.clock ≤ 2080 + continuationPrice + 1 := by
  obtain ⟨callee, called, nodeLocal, nibsLocal, lengthLocal⟩ := environment source.code.lookup node nibs length (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have cost := Graph.body_cost entry graph node nibs length key member nodeLocal nibsLocal lengthLocal installed
  exact Input.ClockCost.scoped_current source name resultShape (ofString "trie_walk") arguments _ body continuation callee resultShape
    2080 continuationPrice args called cost priced

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.environment
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.call_cost
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.scoped_cost
