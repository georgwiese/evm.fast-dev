import InitECandidate.Solver.Mpt.TrieLookupCost

namespace InitECandidate.Solver.Mpt.TrieLookup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def values (root key : BitVec 64) : List (ValueHOL 64) := [.val (.word root), .val (.word key)]
def rawLocals (root key : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "key_hash32" then some (.val (.word key)) else
  if name = ofString "root" then some (.val (.word root)) else none

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (root key : BitVec 64) (known : table (ofString "trie_lookup") = some (formals, body, TrieWalk.resultShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "trie_lookup") (values root key) = some (body, callee, TrieWalk.resultShape) ∧
      callee.lookup (ofString "root") = some (.val (.word root)) ∧ callee.lookup (ofString "key_hash32") = some (.val (.word key)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values root key).length ∧
      ((formals.zip (values root key)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact table (ofString "trie_lookup") (values root key) = some (body, rawLocals root key, TrieWalk.resultShape) := by
    simp only [lookupCodeHOLExact, known, valid]
    rfl
  obtain ⟨callee, called, locals⟩ := CodeEnvironment.finite_lookup table
    (ofString "trie_lookup") (values root key) body (rawLocals root key) TrieWalk.resultShape raw
  refine ⟨callee, called, ?_, ?_⟩
  · rw [locals]
    simp [rawLocals, show ofString "root" ≠ ofString "key_hash32" from by decide]
  · rw [locals]
    simp [rawLocals]

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root key out : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid root) (protectedGraph : graph.Protected out)
    (scratch : source.globals.lookup (ofString "mpt_nib_scratch") = some (.val (.word out)))
    (little : source.be = false) (fits : out.toNat + 64 < 2^64)
    (inputMapped : ∀ offset < 32, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress key offset)))
    (outputMapped : ∀ offset < 64, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress out offset)))
    (separate : ∀ left < 32, ∀ right < 64, byteAddress key left ≠ byteAddress out right)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values root key))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock - (evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "trie_lookup") arguments)).2.clock ≤ 2091 := by
  obtain ⟨callee, called, rootLocal, keyLocal⟩ := environment source.code.lookup root key (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have cost := body_cost entry root key out graph member protectedGraph rootLocal keyLocal scratch little fits inputMapped outputMapped separate installed
  exact Input.ClockCost.call_current source destination (ofString "trie_lookup") arguments _ body callee TrieWalk.resultShape 2090 args called cost

theorem scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root key out : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid root) (protectedGraph : graph.Protected out)
    (scratch : source.globals.lookup (ofString "mpt_nib_scratch") = some (.val (.word out)))
    (little : source.be = false) (fits : out.toNat + 64 < 2^64)
    (inputMapped : ∀ offset < 32, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress key offset)))
    (outputMapped : ∀ offset < 64, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress out offset)))
    (separate : ∀ left < 32, ∀ right < 64, byteAddress key left ≠ byteAddress out right)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (continuationPrice : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values root key))
    (installed : Input.OriginalCode.Installed source.code)
    (priced : Input.ClockCost.Bound source.code continuation continuationPrice) :
    source.clock - (evaluateHOLFiniteState source (.decCall name TrieWalk.resultShape (ofString "trie_lookup") arguments continuation)).2.clock ≤ 2090 + continuationPrice + 1 := by
  obtain ⟨callee, called, rootLocal, keyLocal⟩ := environment source.code.lookup root key (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have cost := body_cost entry root key out graph member protectedGraph rootLocal keyLocal scratch little fits inputMapped outputMapped separate installed
  exact Input.ClockCost.scoped_current source name TrieWalk.resultShape (ofString "trie_lookup") arguments _ body continuation callee TrieWalk.resultShape
    2090 continuationPrice args called cost priced

end InitECandidate.Solver.Mpt.TrieLookup

#print axioms InitECandidate.Solver.Mpt.TrieLookup.environment
#print axioms InitECandidate.Solver.Mpt.TrieLookup.call_cost
#print axioms InitECandidate.Solver.Mpt.TrieLookup.scoped_cost
