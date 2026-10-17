import InitECandidate.Solver.WitnessRadix.Keccak256Execution

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def hashingEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp : BitVec 64) :
    PanSemStateFiniteExact 64 Guest.HostMemory := bind (clearedState (bind source "stp" stp) stp) "i" 0#64

def hashingExit (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp : BitVec 64)
    (finished : PanSemStateFiniteExact 64 Guest.HostMemory) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  restore source "stp" (restore (clearedState (bind source "stp" stp) stp) "i" finished)

theorem hashingEntry_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp : BitVec 64)
    (name : String) (stateDifferent : ofString "stp" ≠ ofString name) (indexDifferent : ofString "i" ≠ ofString name) :
    (hashingEntry source stp).locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
  rw [hashingEntry, bind_lookup_other _ "i" name _ indexDifferent]
  exact bind_lookup_other source "stp" name stp stateDifferent

theorem hashingEntry_args (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer out : BitVec 64)
    (length : Nat) (locals : EntryLocals source pointer out length) : Args (hashingEntry source stp) stp pointer length := by
  constructor
  · rw [hashingEntry, bind_lookup_other _ "i" "stp" _ (by decide)]
    exact bind_lookup_same source "stp" stp
  · exact (hashingEntry_other source stp "p" (by decide) (by decide)).trans locals.pointerLocal
  · exact (hashingEntry_other source stp "n" (by decide) (by decide)).trans locals.lengthLocal

/-- Compose actual supplied block/tail executions with the literal clearing
call and both lexical scopes of the fixed keccak256 function. -/
theorem body_from_blocks (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (stp pointer scratch out : BitVec 64) (length : Nat)
    (data : EntryData source stp pointer scratch out length) (enough : 8 ≤ source.clock)
    (afterLoop finished : PanSemStateFiniteExact 64 Guest.HostMemory)
    (loopRun : evaluateHOLFiniteState (hashingEntry source stp) blocks = (none, afterLoop))
    (loopClock : afterLoop.clock ≤ (hashingEntry source stp).clock)
    (tailRun : evaluateHOLFiniteState afterLoop afterBlocks = (some (.returned (.val (.word 0#64))), finished)) :
    evaluateHOLFiniteState source body =
      (some (.returned (.val (.word 0#64))), hashingExit source stp finished) := by
  classical
  let initial := bind source "stp" stp
  let cleared := clearedState initial stp
  let entry := hashingEntry source stp
  have sequence : evaluateHOLFiniteState entry (.seq blocks afterBlocks) =
      (some (.returned (.val (.word 0#64))), finished) :=
    (StateSteps.next_sequence entry afterLoop _ _ loopRun loopClock).trans tailRun
  have declared : evaluateHOLFiniteState cleared
      (.dec (ofString "i") .one (.const 0#64) (.seq blocks afterBlocks)) =
      (some (.returned (.val (.word 0#64))), restore cleared "i" finished) := by
    rw [evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
    change (let result := evaluateHOLFiniteState entry (.seq blocks afterBlocks)
      (result.1, restore cleared "i" result.2)) = _
    rw [sequence]
  have initialStp := bind_lookup_same source "stp" stp
  have zeroArgs : evalListHOLFinite initial
      (h := fun query => Classical.propDecidable (initial.memaddrs query))
      [localVar "stp", .const 200#64] = some (Zero.values stp 200) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, toExact, initialStp, Zero.values, initial]
  have zeroRun : evaluateHOLFiniteState initial
      (.call (some (none, none)) (ofString "memzero") [localVar "stp", .const 200#64]) = (none, cleared) :=
    Zero.call_execute initial _ stp 200 zeroArgs data.zeroCode (by decide) (by decide)
      data.stateAligned data.zeroMapped enough
  have front := (StateSteps.next_sequence initial cleared _ _ zeroRun
    (by change source.clock - 8 ≤ source.clock; omega)).trans declared
  rw [body_shape, evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, toExact, data.stateGlobal, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let result := (evaluateHOLFiniteState initial
      (.seq (.call (some (none, none)) (ofString "memzero") [localVar "stp", .const 200#64])
        (.dec (ofString "i") .one (.const 0#64) (.seq blocks afterBlocks))))
    (result.1, restore source "stp" result.2)) = _
  rw [front]
  rfl

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.hashingEntry_other
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.hashingEntry_args
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.body_from_blocks
