import InitECandidate.Solver.WitnessRadix.KeccakAbsorbState

namespace InitECandidate.Solver.WitnessRadix.KeccakAbsorb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

def isUnaligned (blk : BitVec 64) : Bool := decide (blk &&& 7#64 ≠ 0#64)
noncomputable def prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk : BitVec 64) :
    PanSemStateFiniteExact 64 Guest.HostMemory := stateLanes (bind source "i" 0#64) stp (isUnaligned blk) 0 17
noncomputable def after (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk : BitVec 64) (bytes : List (BitVec 8)) :
    PanSemStateFiniteExact 64 Guest.HostMemory := { Keccak.post (prepared source stp blk) stp bytes with clock := source.clock-18 }
noncomputable def target (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk : BitVec 64) (bytes : List (BitVec 8)) :
    PanSemStateFiniteExact 64 Guest.HostMemory := restore source "i" (emptyLocalsHOLFinite (after source stp blk bytes))

theorem alignment_read {F : Type} (source : PanSemStateFiniteExact 64 F) (blk : BitVec 64)
    (blkLocal : source.locals.lookup (ofString "blk") = some (.val (.word blk))) :
    eval source alignment = some (.val (.word (if isUnaligned blk then 0#64 else 1#64))) := by
  by_cases mask : blk &&& 7#64 = 0#64
  all_goals simp [eval, alignment, localVar, evalHOLExact, evalListHOLExact, toExact, blkLocal,
    valueIsWord, valueWord, wordOpHOL, wordOp, AndOp.and, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, isUnaligned, mask]

/-- The entire literal fixed block absorber, including alignment choice,
all 17 XOR lanes, real permutation call, lexical scope and return. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk : BitVec 64)
    (stpLocal : source.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (blkLocal : source.locals.lookup (ofString "blk") = some (.val (.word blk)))
    (mapped : Mapped source stp blk (isUnaligned blk))
    (code : source.code.lookup (ofString "keccak_f1600") = some (Keccak.formals, Keccak.f1600Body, .one))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle) (aligned : stp.toNat%8=0) (fits : stp.toNat+200 < 2^64)
    (enough : 18 ≤ source.clock) :
    ∃ bytes : List (BitVec 8), bytes.length=200 ∧
      evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))), target source stp blk bytes) := by
  classical
  let initial := bind source "i" 0#64
  let lanes := prepared source stp blk
  have stp' : initial.locals.lookup (ofString "stp") = some (.val (.word stp)) :=
    (bind_lookup_other source "i" "stp" _ (by decide)).trans stpLocal
  have blk' : initial.locals.lookup (ofString "blk") = some (.val (.word blk)) :=
    (bind_lookup_other source "i" "blk" _ (by decide)).trans blkLocal
  have mapped' : Mapped initial stp blk (isUnaligned blk) := ⟨mapped.stateWords,mapped.blockWords,mapped.blockBytes⟩
  have loopRun := loop_execute initial stp blk (isUnaligned blk) 0 17 rfl stp' blk' (bind_lookup_same _ _ _) mapped' (by change 17 ≤ source.clock; omega)
  have read := alignment_read initial blk blk'
  simp only [eval] at read
  have chosen : evaluateHOLFiniteState initial (.ite alignment (loop false) (loop true)) = (none,lanes) := by
    change evaluateHOLFiniteState initial (.ite alignment (loop false) (loop true)) =
      (none,stateLanes initial stp (isUnaligned blk) 0 17)
    rw [evaluateHOLFiniteState_ite,read]
    cases choice : isUnaligned blk <;> simp only [choice, Bool.false_eq_true, ↓reduceIte] at loopRun ⊢
    · simpa using loopRun
    · simpa using loopRun
  have frame := stateLanes_control initial stp (isUnaligned blk) 0 17
  have lanesCode : lanes.code.lookup (ofString "keccak_f1600") = some (Keccak.formals,Keccak.f1600Body,.one) := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code.lookup (ofString "keccak_f1600")) frame
    exact h.trans code
  have lanesOracle : lanes.ffi.oracle = InitE.sourceOracle := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.ffi.oracle) frame
    exact h.trans oracleEq
  have lanesLocal : lanes.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
    have h := stateLanes_other initial stp (isUnaligned blk) 0 17 (ofString "stp") (by decide)
    exact h.trans stp'
  have args : evalListHOLFinite lanes (h := fun address => Classical.propDecidable (lanes.memaddrs address)) [localVar "stp"] = some (Keccak.values stp) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLFinite,evalHOLExact,localVar,toExact,lanesLocal,Keccak.values]
  have lanesMapped : ∀ word : Fin 25, lanes.memaddrs (byteAddress stp (8*word.val)) := by
    intro word
    have h : lanes.memaddrs = source.memaddrs := stateLanes_domain initial stp (isUnaligned blk) 0 17
    rw [h]
    exact mapped.stateWords word
  have lanesClock : lanes.clock = source.clock-17 := stateLanes_clock initial stp (isUnaligned blk) 0 17
  obtain ⟨bytes,length,permRun⟩ := Keccak.call_execute lanes [localVar "stp"] stp args lanesCode lanesOracle aligned fits lanesMapped
    (by rw [lanesClock]; omega)
  have clockEq : lanes.clock-1 = source.clock-18 := by
    rw [lanesClock]
    omega
  rw [clockEq] at permRun
  change evaluateHOLFiniteState lanes (.call (some (none,none)) (ofString "keccak_f1600") [localVar "stp"]) =
    (none,after source stp blk bytes) at permRun
  have tailRun : evaluateHOLFiniteState lanes tail =
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (after source stp blk bytes)) := by
    rw [tail, StateSteps.next_sequence lanes (after source stp blk bytes) _ _ permRun (by
      change source.clock-18 ≤ lanes.clock
      rw [lanesClock]
      omega)]
    exact BuildEntry.zero_return _
  have sequence := (StateSteps.next_sequence initial lanes _ _ chosen (by
    rw [lanesClock]
    change source.clock-17 ≤ source.clock
    omega)).trans tailRun
  refine ⟨bytes,length,?_⟩
  rw [body_shape,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,↓reduceIte]
  change (let output := (evaluateHOLFiniteState initial (.seq (.ite alignment (loop false) (loop true)) tail))
    (output.1,restore source "i" output.2)) = _
  rw [sequence]
  rfl

end InitECandidate.Solver.WitnessRadix.KeccakAbsorb

#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.alignment_read
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.execute
