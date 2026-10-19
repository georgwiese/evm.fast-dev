import InitECandidate.Solver.Mpt.KeyToNibblesNormal
import InitECandidate.Solver.Input.ClockCostCurrentCall
import InitECandidate.Solver.Input.IgnoredCallNormal

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def values (key out : BitVec 64) : List (ValueHOL 64) := [.val (.word key), .val (.word 32#64), .val (.word out)]
def rawLocals (key out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "out" then some (.val (.word out)) else
  if name = ofString "n" then some (.val (.word 32#64)) else
  if name = ofString "key" then some (.val (.word key)) else none

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (key out : BitVec 64) (known : table (ofString "key_to_nibbles") = some (formals, body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "key_to_nibbles") (values key out) = some (body, callee, .one) ∧
      callee.lookup (ofString "key") = some (.val (.word key)) ∧ callee.lookup (ofString "out") = some (.val (.word out)) ∧
      callee.lookup (ofString "n") = some (.val (.word 32#64)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values key out).length ∧
      ((formals.zip (values key out)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact table (ofString "key_to_nibbles") (values key out) = some (body, rawLocals key out, .one) := by
    simp only [lookupCodeHOLExact, known, valid]
    rfl
  obtain ⟨callee, called, locals⟩ := CodeEnvironment.finite_lookup table
    (ofString "key_to_nibbles") (values key out) body (rawLocals key out) .one raw
  refine ⟨callee, called, ?_, ?_, ?_⟩
  · rw [locals]
    simp [rawLocals, show ofString "key" ≠ ofString "out" from by decide, show ofString "key" ≠ ofString "n" from by decide]
  · rw [locals]
    simp [rawLocals]
  · rw [locals]
    simp [rawLocals, show ofString "n" ≠ ofString "out" from by decide]

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64)
    (little : source.be = false) (fits : out.toNat + 64 < 2^64)
    (inputMapped : ∀ offset < 32, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress key offset)))
    (outputMapped : ∀ offset < 64, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress out offset)))
    (separate : ∀ left < 32, ∀ right < 64, byteAddress key left ≠ byteAddress out right)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values key out))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock - (evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "key_to_nibbles") arguments)).2.clock ≤ 9 := by
  obtain ⟨callee, called, keyLocal, outLocal, lengthLocal⟩ := environment source.code.lookup key out (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have cost := body_cost entry key out keyLocal outLocal lengthLocal little fits inputMapped outputMapped separate
  exact Input.ClockCost.call_current source destination (ofString "key_to_nibbles") arguments _ body callee .one 8 args called cost

theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64)
    (little : source.be = false) (fits : out.toNat + 64 < 2^64)
    (inputMapped : ∀ offset < 32, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress key offset)))
    (outputMapped : ∀ offset < 64, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress out offset)))
    (separate : ∀ left < 32, ∀ right < 64, byteAddress key left ≠ byteAddress out right)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values key out))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "key_to_nibbles") arguments) = (none, post)) :
    9 ≤ source.clock ∧ post.clock = source.clock - 9 ∧ post.locals = source.locals ∧
      TrieWalk.KeyView post.memory post.memaddrs post.be out 64 ∧ OutputFrame source post out := by
  obtain ⟨callee, called, keyLocal, outLocal, lengthLocal⟩ := environment source.code.lookup key out (original_code source.code installed)
  obtain ⟨positive, target, returned, bodyRun⟩ := Input.CallNormal.ignored_callee_return source post (ofString "key_to_nibbles") arguments _ body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨funded, clock, answer, view, frame⟩ := body_normal entry target key out keyLocal outLocal lengthLocal little fits inputMapped outputMapped separate returned bodyRun
  rw [answer] at bodyRun
  have actual : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "key_to_nibbles") arguments) =
      (none, {target with locals := source.locals}) := by
    rw [evaluateHOLFiniteState_call, args]
    simp only
    rw [called]
    simp only
    rw [if_neg (show source.clock ≠ 0 from by omega), bodyRun]
    simp [shapeOfHOLExact, shapeEqHOL]
  have postEq := congrArg Prod.snd (normal.symm.trans actual)
  change post = {target with locals := source.locals} at postEq
  change 8 ≤ source.clock - 1 at funded
  change target.clock = source.clock - 1 - 8 at clock
  rw [postEq]
  exact ⟨by omega, by change target.clock = source.clock - 9; omega, rfl, view, ⟨frame.fields, frame.memory⟩⟩

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.environment
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.call_cost
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.call_normal
