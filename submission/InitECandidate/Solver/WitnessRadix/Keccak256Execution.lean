import InitECandidate.Solver.WitnessRadix.Keccak256Entry

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def price (length : Nat) : Nat := 202+20*(length/136)
def clearedState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  {source with memory := Zero.finalMemory source.memory stp 200,clock := source.clock-8}

/-- Complete fixed keccak256 from actual ABI/code/globals and mapped buffer
facts, including clearing, arbitrary full blocks, padding/output and scopes.
The source-clock cost is at most202+20*floor(length/136). -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer scratch out : BitVec 64) (length : Nat)
    (locals : EntryLocals source pointer out length) (data : EntryData source stp pointer scratch out length)
    (small : length+136<2^64) (enough : price length≤source.clock) :
    ∃ output : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source body=(some (.returned (.val (.word 0#64))),output) ∧
      output.clock≤source.clock ∧ source.clock-price length≤output.clock ∧ KeccakAbsorb.hashControl output=KeccakAbsorb.hashControl source ∧
      ∀ query,Protected stp scratch out query → output.memory query=source.memory query := by
  classical
  let initial := bind source "stp" stp
  let cleared := clearedState initial stp
  let entry := bind cleared "i" 0#64
  have entryOther (name : String) (stateDifferent : ofString "stp"≠ofString name) (indexDifferent : ofString "i"≠ofString name) :
      entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    change (bind cleared "i" 0#64).locals.lookup (ofString name)=_
    rw [bind_lookup_other cleared "i" name 0#64 indexDifferent]
    exact bind_lookup_other source "stp" name stp stateDifferent
  have entryStp : entry.locals.lookup (ofString "stp")=some (.val (.word stp)) := by
    change (bind cleared "i" 0#64).locals.lookup (ofString "stp")=_
    rw [bind_lookup_other cleared "i" "stp" 0#64 (by decide)]
    exact bind_lookup_same source "stp" stp
  have entryArgs : Args entry stp pointer length :=
    ⟨entryStp,(entryOther "p" (by decide) (by decide)).trans locals.pointerLocal,
      (entryOther "n" (by decide) (by decide)).trans locals.lengthLocal⟩
  have entryOut : entry.locals.lookup (ofString "out")=some (.val (.word out)) :=
    (entryOther "out" (by decide) (by decide)).trans locals.outputLocal
  have entryData := EntryData.of_control source entry stp pointer scratch out length rfl data
  have div := Nat.mod_add_div length 136
  have rem := Nat.mod_lt length (by decide : 0<136)
  obtain ⟨afterLoop,loopRun,loopClock,loopControl,loopIndex,loopOther,loopMemory⟩ := loop_execute entry stp pointer 0 length (length/136)
    entryArgs entryData.hashCode entryData.blockMapped (bind_lookup_same _ _ _) small (by omega) (by omega)
    data.stateAligned data.stateFits (by change 20*(length/136)≤source.clock-8; unfold price at enough; omega)
  let index := 136*(length/136)
  have ordered : index≤length := by dsimp [index]; omega
  have remBound : length-index<136 := by dsimp [index]; omega
  have afterArgs : Args afterLoop stp pointer length :=
    ⟨(loopOther (ofString "stp") (by decide)).trans entryArgs.stateLocal,
      (loopOther (ofString "p") (by decide)).trans entryArgs.pointerLocal,
      (loopOther (ofString "n") (by decide)).trans entryArgs.lengthLocal⟩
  have afterOut : afterLoop.locals.lookup (ofString "out")=some (.val (.word out)) :=
    (loopOther (ofString "out") (by decide)).trans entryOut
  have afterIndex : afterLoop.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) := by
    simpa only [Nat.zero_add] using loopIndex
  have afterData := EntryData.of_control entry afterLoop stp pointer scratch out length loopControl entryData
  obtain ⟨finished,tailRun,tailUpper,tailLower,tailControl,tailMemory⟩ := after_blocks_execute afterLoop stp pointer scratch out index length
    afterArgs afterOut afterIndex (by omega) ordered remBound (afterData.tailData index ordered remBound)
    (by rw [loopClock]; change 194≤source.clock-8-20*(length/136); unfold price at enough; omega)
  have sequence : evaluateHOLFiniteState entry (.seq blocks afterBlocks)=(some (.returned (.val (.word 0#64))),finished) :=
    (StateSteps.next_sequence entry afterLoop _ _ loopRun (by rw [loopClock]; omega)).trans tailRun
  have declared : evaluateHOLFiniteState cleared (.dec (ofString "i") .one (.const 0#64) (.seq blocks afterBlocks))=
      (some (.returned (.val (.word 0#64))),restore cleared "i" finished) := by
    rw [evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,↓reduceIte]
    change (let result := (evaluateHOLFiniteState entry (.seq blocks afterBlocks))
      (result.1,restore cleared "i" result.2))=_
    rw [sequence]
  have initialStp : initial.locals.lookup (ofString "stp")=some (.val (.word stp)) := bind_lookup_same source "stp" stp
  have zeroArgs : evalListHOLFinite initial (h := fun address => Classical.propDecidable (initial.memaddrs address))
      [localVar "stp",.const 200#64]=some (Zero.values stp 200) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,initialStp,Zero.values]
  have zeroRun : evaluateHOLFiniteState initial (.call (some (none,none)) (ofString "memzero") [localVar "stp",.const 200#64])=(none,cleared) :=
    Zero.call_execute initial _ stp 200 zeroArgs data.zeroCode (by decide) (by decide) data.stateAligned data.zeroMapped
      (by change 8≤source.clock; unfold price at enough; omega)
  have front := (StateSteps.next_sequence initial cleared _ _ zeroRun (by change source.clock-8≤source.clock; omega)).trans declared
  let final := restore source "stp" (restore cleared "i" finished)
  refine ⟨final,?_,?_,?_,?_,?_⟩
  · rw [body_shape,evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,toExact,data.stateGlobal,shapeOfHOLExact,shapeEqHOL,↓reduceIte]
    change (let result := (evaluateHOLFiniteState initial
        (.seq (.call (some (none,none)) (ofString "memzero") [localVar "stp",.const 200#64])
          (.dec (ofString "i") .one (.const 0#64) (.seq blocks afterBlocks))))
      (result.1,restore source "stp" result.2))=_
    rw [front]
  · change finished.clock≤source.clock
    rw [loopClock] at tailUpper
    change finished.clock≤source.clock-8-20*(length/136) at tailUpper
    omega
  · change source.clock-price length≤finished.clock
    rw [loopClock] at tailLower
    change source.clock-8-20*(length/136)-194≤finished.clock at tailLower
    unfold price
    omega
  · exact (KeccakAbsorb.hashControl_restore source _ "stp").trans
      ((KeccakAbsorb.hashControl_restore cleared finished "i").trans (tailControl.trans loopControl))
  · intro query protection
    have tail := tailMemory query (Protected.tail stp scratch out query protection)
    have loopFrame := loopMemory query (Protected.tail stp scratch out query protection).1
    have zeroFrame : entry.memory query=source.memory query :=
      Zero.final_memory_away source.memory stp query 200 (by intro offset inside; exact (protection.1 offset inside).1)
    exact tail.trans (loopFrame.trans zeroFrame)

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.execute
