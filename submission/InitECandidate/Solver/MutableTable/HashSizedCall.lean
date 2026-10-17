import InitECandidate.Solver.MutableTable.HashSizedExecution

namespace InitECandidate.Solver.MutableTable.HashSized
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def values (kind : Kind) (pointer : BitVec 64) : List (ValueHOL 64) :=
  [.val (.word pointer), .val (.word (BitVec.ofNat 64 (keySize kind)))]
def rawLocals (kind : Kind) (pointer : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "key_len" then some (.val (.word (BitVec.ofNat 64 (keySize kind)))) else
  if name = ofString "p" then some (.val (.word pointer)) else none

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (kind : Kind) (pointer : BitVec 64) (known : table (ofString "htab_hash") = some (Hash.formals, Hash.body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "htab_hash") (values kind pointer) = some (Hash.body, callee, .one) ∧
      callee.lookup (ofString "p") = some (.val (.word pointer)) ∧
      callee.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (keySize kind)))) := by
  have valid : (Hash.formals.map Prod.fst).Nodup ∧ Hash.formals.length = (values kind pointer).length ∧
      ((Hash.formals.zip (values kind pointer)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [Hash.formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact table (ofString "htab_hash") (values kind pointer) = some (Hash.body, rawLocals kind pointer, .one) := by
    simp only [lookupCodeHOLExact, known, valid]
    rfl
  obtain ⟨callee, called, locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup table
    (ofString "htab_hash") (values kind pointer) Hash.body (rawLocals kind pointer) .one raw
  refine ⟨callee, called, ?_, ?_⟩
  · rw [locals]
    simp [rawLocals, show ofString "p" ≠ ofString "key_len" from by decide]
  · rw [locals]
    simp [rawLocals]

/-- Real aligned account/storage hash caller, exact result, one source clock. -/
theorem aligned_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (pointer : BitVec 64)
    (words : Fin 6 → BitVec 64) (bytes : Fin 4 → UInt8) (name : String)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values kind pointer))
    (known : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (aligned : pointer &&& 7#64 = 0#64)
    (mapped : ∀ i : Fin 6, i.val < wordCount kind → source.memaddrs (pointer + BitVec.ofNat 64 (8 * i.val)))
    (stored : ∀ i : Fin 6, i.val < wordCount kind → source.memory (pointer + BitVec.ofNat 64 (8 * i.val)) = .word (words i))
    (loaded : ∀ i : Fin 4, @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be
      (pointer + BitVec.ofNat 64 (8 * wordCount kind + i.val)) = some (bytes i))
    (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_hash") arguments continuation) =
      (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind {source with clock := source.clock - 1}
        name (resultWord kind words bytes)) continuation
       (output.1, restore source name output.2)) := by
  obtain ⟨callee, called, p, length⟩ := environment source.code.lookup kind pointer known
  let entry := callEntryStateHOLFinite source callee
  have run := aligned_execute entry kind pointer words bytes p length aligned mapped stored loaded
  have actual := Input.CallNormal.pure_return_execute source (closed entry) name (ofString "htab_hash") arguments _ Hash.body
    continuation callee (resultWord kind words bytes) 0 args called enough run (canonical entry)
  simpa only [Nat.sub_zero] using actual

/-- Real unaligned account/storage hash caller, including byte macros and ABI. -/
theorem unaligned_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (pointer : BitVec 64)
    (bytes : Fin 52 → UInt8) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values kind pointer))
    (known : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (unaligned : pointer &&& 7#64 ≠ 0#64)
    (loaded : ∀ i : Fin 52, i.val < keySize kind → @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be
      (pointer + BitVec.ofNat 64 i.val) = some (bytes i))
    (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_hash") arguments continuation) =
      (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind {source with clock := source.clock - 1}
        name (resultWord kind (packedWords bytes) (tailBytes kind bytes))) continuation
       (output.1, restore source name output.2)) := by
  obtain ⟨callee, called, p, length⟩ := environment source.code.lookup kind pointer known
  let entry := callEntryStateHOLFinite source callee
  have run := unaligned_execute entry kind pointer bytes p length unaligned loaded
  have actual := Input.CallNormal.pure_return_execute source (closed entry) name (ofString "htab_hash") arguments _ Hash.body
    continuation callee (resultWord kind (packedWords bytes) (tailBytes kind bytes)) 0 args called enough run (canonical entry)
  simpa only [Nat.sub_zero] using actual

end InitECandidate.Solver.MutableTable.HashSized

#print axioms InitECandidate.Solver.MutableTable.HashSized.environment
#print axioms InitECandidate.Solver.MutableTable.HashSized.aligned_call
#print axioms InitECandidate.Solver.MutableTable.HashSized.unaligned_call
