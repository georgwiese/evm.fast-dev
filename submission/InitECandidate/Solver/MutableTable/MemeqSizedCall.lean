import InitECandidate.Solver.MutableTable.MemeqSizedReads
import InitECandidate.Solver.WitnessRadix.MemeqEnvironment
import InitECandidate.Solver.Input.PureReturn

namespace InitECandidate.Solver.MutableTable.MemeqSized
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

def values (kind : Kind) (a b : BitVec 64) : List (ValueHOL 64) :=
  [.val (.word a), .val (.word b), .val (.word (BitVec.ofNat 64 (keySize kind)))]
def rawLocals (kind : Kind) (a b : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "n" then some (.val (.word (BitVec.ofNat 64 (keySize kind)))) else
  if name = ofString "b" then some (.val (.word b)) else
  if name = ofString "a" then some (.val (.word a)) else none

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (kind : Kind) (a b : BitVec 64) (known : table (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "memeq") (values kind a b) = some (Memeq32.body, callee, .one) ∧
      callee.lookup (ofString "a") = some (.val (.word a)) ∧ callee.lookup (ofString "b") = some (.val (.word b)) ∧
      callee.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 (keySize kind)))) := by
  have valid : (Memeq32.formals.map Prod.fst).Nodup ∧ Memeq32.formals.length = (values kind a b).length ∧
      ((Memeq32.formals.zip (values kind a b)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [Memeq32.formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact table (ofString "memeq") (values kind a b) = some (Memeq32.body, rawLocals kind a b, .one) := by
    simp only [lookupCodeHOLExact, known, valid]
    rfl
  obtain ⟨callee, called, locals⟩ := CodeEnvironment.finite_lookup table
    (ofString "memeq") (values kind a b) Memeq32.body (rawLocals kind a b) .one raw
  refine ⟨callee, called, ?_, ?_, ?_⟩
  · rw [locals]
    simp [rawLocals, show ofString "a" ≠ ofString "b" from by decide, show ofString "a" ≠ ofString "n" from by decide]
  · rw [locals]
    simp [rawLocals, show ofString "b" ≠ ofString "n" from by decide]
  · rw [locals]
    simp [rawLocals]

/-- The real aligned20/52-byte memeq call, including each actual memory read,
early return, ABI check and lexical scope. One caller source clock. -/
theorem aligned_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (a b : BitVec 64)
    (left right : Fin 6 → BitVec 64) (leftBytes rightBytes : Fin 4 → UInt8) (name : String)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values kind a b))
    (known : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (aligned : (a ||| b) &&& 7#64 = 0#64)
    (leftData : Data source kind a left leftBytes) (rightData : Data source kind b right rightBytes)
    (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "memeq") arguments continuation) =
      (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind {source with clock := source.clock - 1} name
        (if CompareChain.agrees (checks kind left right leftBytes rightBytes) then 1#64 else 0#64)) continuation
       (output.1, restore source name output.2)) := by
  obtain ⟨callee, called, aLocal, bLocal, length⟩ := environment source.code.lookup kind a b known
  let entry := callEntryStateHOLFinite source callee
  have entryLeft : Data entry kind a left leftBytes := ⟨leftData.mapped, leftData.stored, leftData.trailing⟩
  have entryRight : Data entry kind b right rightBytes := ⟨rightData.mapped, rightData.stored, rightData.trailing⟩
  have run := aligned_of_data entry kind a b left right leftBytes rightBytes aLocal bLocal length aligned entryLeft entryRight
  have frame : emptyLocalsHOLFinite (restore entry "i" (emptyLocalsHOLFinite (WitnessRadix.QueryBranch.bind entry "i" 0#64))) = emptyLocalsHOLFinite entry := rfl
  have actual := Input.CallNormal.pure_return_execute source _ name (ofString "memeq") arguments _ Memeq32.body continuation callee
    (if CompareChain.agrees (checks kind left right leftBytes rightBytes) then 1#64 else 0#64) 0 args called enough run frame
  simpa only [Nat.sub_zero] using actual

end InitECandidate.Solver.MutableTable.MemeqSized

#print axioms InitECandidate.Solver.MutableTable.MemeqSized.environment
#print axioms InitECandidate.Solver.MutableTable.MemeqSized.aligned_call
